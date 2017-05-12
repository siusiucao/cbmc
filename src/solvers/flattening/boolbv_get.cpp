/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/threeval.h>
#include <util/std_types.h>
#include <util/simplify_expr.h>

#include "boolbv.h"
#include "boolbv_type.h"

/*******************************************************************\

Function: boolbvt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolbvt::get(const exprt &expr) const
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    boolbv_mapt::mappingt::const_iterator it=
      map.mapping.find(identifier);

    if(it!=map.mapping.end())
    {
      const boolbv_mapt::map_entryt &map_entry=it->second;

      if(is_unbounded_array(map_entry.type))
        return bv_get_unbounded_array(expr);

      std::vector<bool> unknown;
      bvt bv;
      std::size_t width=map_entry.width;

      bv.resize(width);
      unknown.resize(width);

      for(std::size_t bit_nr=0; bit_nr<width; bit_nr++)
      {
        ASSERT(bit_nr<map_entry.literal_map.size());

        if(map_entry.literal_map[bit_nr].is_set)
        {
          unknown[bit_nr]=false;
          bv[bit_nr]=map_entry.literal_map[bit_nr].l;
        }
        else
        {
          unknown[bit_nr]=true;
          bv[bit_nr].clear();
        }
      }

      return bv_get_rec(bv, unknown, 0, map_entry.type);
    }
  }

  return SUB::get(expr);
}

/*******************************************************************\

Function: boolbvt::bv_get_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolbvt::bv_get_rec(
  const bvt &bv,
  const std::vector<bool> &unknown,
  std::size_t offset,
  const typet &type) const
{
  if(type.id()==ID_symbol)
    return bv_get_rec(bv, unknown, offset, ns.follow(type));

  std::size_t width=boolbv_width(type);

  ASSERT(bv.size()==unknown.size());
  ASSERT(bv.size()>=offset+width);

  if(type.id()==ID_bool)
  {
    if(!unknown[offset])
    {
      switch(prop.l_get(bv[offset]).get_value())
      {
      case tvt::tv_enumt::TV_FALSE: return false_exprt();
      case tvt::tv_enumt::TV_TRUE:  return true_exprt();
      default: return false_exprt(); // default
      }
    }

    return nil_exprt();
  }

  bvtypet bvtype=get_bvtype(type);

  if(bvtype==IS_UNKNOWN)
  {
    if(type.id()==ID_array)
    {
      const typet &subtype=type.subtype();
      std::size_t sub_width=boolbv_width(subtype);

      if(sub_width!=0)
      {
        exprt::operandst op;
        op.reserve(width/sub_width);

        for(std::size_t new_offset=0;
            new_offset<width;
            new_offset+=sub_width)
        {
          op.push_back(
            bv_get_rec(bv, unknown, offset+new_offset, subtype));
        }

        exprt dest=exprt(ID_array, type);
        dest.operands().swap(op);
        return dest;
      }
    }
    else if(type.id()==ID_struct_tag)
    {
      return
        bv_get_rec(
          bv, unknown, offset, ns.follow_tag(to_struct_tag_type(type)));
    }
    else if(type.id()==ID_union_tag)
    {
      return
        bv_get_rec(
          bv, unknown, offset, ns.follow_tag(to_union_tag_type(type)));
    }
    else if(type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(type);
      const struct_typet::componentst &components=struct_type.components();
      std::size_t new_offset=0;
      exprt::operandst op;
      op.reserve(components.size());

      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        const typet &subtype=ns.follow(it->type());
        op.push_back(nil_exprt());

        std::size_t sub_width=boolbv_width(subtype);

        if(sub_width!=0)
        {
          op.back()=bv_get_rec(bv, unknown, offset+new_offset, subtype);
          new_offset+=sub_width;
        }
      }

      struct_exprt dest(type);
      dest.operands().swap(op);
      return dest;
    }
    else if(type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(type);
      const union_typet::componentst &components=union_type.components();

      ASSERT(!components.empty());

      // Any idea that's better than just returning the first component?
      std::size_t component_nr=0;

      union_exprt value(union_type);

      value.set_component_name(
        components[component_nr].get_name());

      const typet &subtype=components[component_nr].type();

      value.op()=bv_get_rec(bv, unknown, offset, subtype);

      return value;
    }
    else if(type.id()==ID_vector)
    {
      const typet &subtype=ns.follow(type.subtype());
      std::size_t sub_width=boolbv_width(subtype);

      if(sub_width!=0 && width%sub_width==0)
      {
        std::size_t size=width/sub_width;
        exprt value(ID_vector, type);
        value.reserve_operands(size);

        for(std::size_t i=0; i<size; i++)
          value.operands().push_back(
            bv_get_rec(bv, unknown, i*sub_width, subtype));

        return value;
      }
    }
    else if(type.id()==ID_complex)
    {
      const typet &subtype=ns.follow(type.subtype());
      std::size_t sub_width=boolbv_width(subtype);

      if(sub_width!=0 && width==sub_width*2)
      {
        exprt value(ID_complex, type);
        value.operands().resize(2);

        value.op0()=bv_get_rec(bv, unknown, 0*sub_width, subtype);
        value.op1()=bv_get_rec(bv, unknown, 1*sub_width, subtype);

        return value;
      }
    }
  }

  std::string value;

  for(std::size_t bit_nr=offset; bit_nr<offset+width; bit_nr++)
  {
    char ch;
    if(unknown[bit_nr])
      ch='0';
    else
    {
      switch(prop.l_get(bv[bit_nr]).get_value())
      {
       case tvt::tv_enumt::TV_FALSE: ch='0'; break;
       case tvt::tv_enumt::TV_TRUE:  ch='1'; break;
       case tvt::tv_enumt::TV_UNKNOWN: ch='0'; break;
       default: ASSERT(false);
      }
    }

    value=ch+value;
  }

  switch(bvtype)
  {
  case IS_UNKNOWN:
    if(type.id()==ID_string)
    {
      mp_integer int_value=binary2integer(value, false);
      irep_idt s;
      if(int_value>=string_numbering.size())
        s=irep_idt();
      else
        s=string_numbering[int_value.to_long()];

      return constant_exprt(s, type);
    }
    break;

  case IS_RANGE:
    {
      mp_integer int_value=binary2integer(value, false);
      mp_integer from=string2integer(type.get_string(ID_from));

      constant_exprt value_expr(type);
      value_expr.set_value(integer2string(int_value+from));
      return value_expr;
    }
    break;

  default:
  case IS_C_ENUM:
    constant_exprt value_expr(type);
    value_expr.set_value(value);
    return value_expr;
  }

  return nil_exprt();
}

/*******************************************************************\

Function: boolbvt::bv_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolbvt::bv_get(const bvt &bv, const typet &type) const
{
  std::vector<bool> unknown;
  unknown.resize(bv.size(), false);
  return bv_get_rec(bv, unknown, 0, type);
}

/*******************************************************************\

Function: boolbvt::bv_get_cache

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolbvt::bv_get_cache(const exprt &expr) const
{
  if(expr.type().id()==ID_bool) // boolean?
    return get(expr);

  // look up literals in cache
  bv_cachet::const_iterator it=bv_cache.find(expr);
  if(it==bv_cache.end())
    return nil_exprt();

  return bv_get(it->second, expr.type());
}

/*******************************************************************\

Function: boolbvt::bv_get_unbounded_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolbvt::bv_get_unbounded_array(const exprt &expr) const
{
  // first, try to get size

  const typet &type=expr.type();
  const exprt &size_expr=to_array_type(type).size();
  exprt size=simplify_expr(get(size_expr), ns);

  // no size, give up
  if(size.is_nil())
    return nil_exprt();

  // get the numeric value, unless it's infinity
  mp_integer size_mpint;

  if(size.id()!=ID_infinity)
  {
    if(to_integer(size, size_mpint))
      return nil_exprt();

    // simple sanity check
    if(size_mpint<0)
      return nil_exprt();
  }
  else
    size_mpint=0;

  // search array indices

  typedef std::map<mp_integer, exprt> valuest;
  valuest values;

  {
    std::size_t number;

    if(arrays.get_number(expr, number))
      return nil_exprt();

    // get root
    number=arrays.find_number(number);

    ASSERT(number<index_map.size());
    index_mapt::const_iterator it=index_map.find(number);
    ASSERT(it!=index_map.end());
    const index_sett &index_set=it->second;

    for(index_sett::const_iterator it1=
        index_set.begin();
        it1!=index_set.end();
        it1++)
    {
      index_exprt index;
      index.type()=type.subtype();
      index.array()=expr;
      index.index()=*it1;

      exprt value=bv_get_cache(index);
      exprt index_value=bv_get_cache(*it1);

      if(!index_value.is_nil())
      {
        mp_integer index_mpint;

        if(!to_integer(index_value, index_mpint))
        {
          if(value.is_nil())
            values[index_mpint]=exprt(ID_unknown, type.subtype());
          else
            values[index_mpint]=value;
        }
      }
    }
  }

  exprt result;

  if(size_mpint>100 || size.id()==ID_infinity)
  {
    result=exprt("array-list", type);
    result.type().set(ID_size, integer2string(size_mpint));

    result.operands().reserve(values.size()*2);

    for(valuest::const_iterator it=values.begin();
        it!=values.end();
        it++)
    {
      exprt index=from_integer(it->first, size.type());
      result.copy_to_operands(index, it->second);
    }
  }
  else
  {
    // set the size
    result=exprt(ID_array, type);
    result.type().set(ID_size, size);

    std::size_t size_int=integer2size_t(size_mpint);

    // allocate operands
    result.operands().resize(size_int);

    for(std::size_t i=0; i<size_int; i++)
      result.operands()[i]=exprt(ID_unknown);

    // search uninterpreted functions

    for(valuest::iterator it=values.begin();
        it!=values.end();
        it++)
      if(it->first>=0 && it->first<size_mpint)
        result.operands()[integer2size_t(it->first)].swap(it->second);
  }

  return result;
}

/*******************************************************************\

Function: boolbvt::get_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer boolbvt::get_value(
  const bvt &bv,
  std::size_t offset,
  std::size_t width)
{
  mp_integer value=0;
  mp_integer weight=1;

  for(std::size_t bit_nr=offset; bit_nr<offset+width; bit_nr++)
  {
    ASSERT(bit_nr<bv.size());
    switch(prop.l_get(bv[bit_nr]).get_value())
    {
     case tvt::tv_enumt::TV_FALSE:   break;
     case tvt::tv_enumt::TV_TRUE:    value+=weight; break;
     case tvt::tv_enumt::TV_UNKNOWN: break;
     default: ASSERT(false);
    }

    weight*=2;
  }

  return value;
}
