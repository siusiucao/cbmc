/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <iostream>

#include <util/type.h>
#include <util/std_expr.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>

#include "abstract_object.h"

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

abstract_objectt::abstract_objectt(const typet &type):
type(type), top(true), bottom(false)
{}

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

abstract_objectt::abstract_objectt(const typet &type, bool top, bool bottom):
  type(type), top(top), bottom(bottom)
{
  assert(!(top && bottom));
}

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

abstract_objectt::abstract_objectt(const abstract_objectt &old):
  type(old.type), top(old.top), bottom(old.bottom)
{}

/*******************************************************************\

Function: abstract_objectt::abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object

 Outputs:

 Purpose:

\*******************************************************************/

abstract_objectt::abstract_objectt(const constant_exprt &expr):
type(expr.type()), top(true), bottom(false)
{}

abstract_objectt::~abstract_objectt()
{

}

const typet &abstract_objectt::get_type() const
{
  return type;
}

/*******************************************************************\

Function: abstract_objectt::merge_state

  Inputs:
   op1 - the first abstract object
   op2 - the second abstract object

 Outputs:

 Purpose: Set this abstract object to be the result of merging two
          other abstract objects. This is the worst case - we can
          only set to top or bottom.

\*******************************************************************/

bool abstract_objectt::merge_state(
  const abstract_object_pointert op1, const abstract_object_pointert op2)
{
  top=op1->top||op2->top;
  bottom=op1->bottom && op2->bottom;

  return top!=op1->top || bottom!=op1->bottom;
  assert(!(top && bottom));
}

/*******************************************************************\

Function: abstract_objectt::merge

  Inputs:
   op - the abstract object to merge with

 Outputs:

 Purpose: Set this abstract object to be the result of merging this
          abstract object and the provided one. See merge_state.

\*******************************************************************/

abstract_object_pointert abstract_objectt::merge(
  const abstract_object_pointert op, bool &out_any_modifications)
{
  assert(type==op->type);
  abstract_object_pointert m=abstract_object_pointert(new abstract_objectt(*this));
  out_any_modifications=m->merge_state(abstract_object_pointert(this), op);
  return m;
}

abstract_object_pointert abstract_objectt::expression_transform_binary(
  const exprt &expr, const abstract_environmentt &environment) const
{
  typedef std::function<abstract_object_pointert(const exprt &)> eval_handlert;
  std::map<irep_idt, eval_handlert> handlers=
  {
    {
      ID_equal, [&](const exprt &expr)
      {
        return expression_transform_equals_simple(
          expr.op0(), expr.op1(), environment);
      }
    },
    {
      ID_notequal, [&](const exprt &expr)
      {
        abstract_object_pointert equals=expression_transform_equals_simple(
          expr.op0(), expr.op1(), environment);
        const exprt &result=equals->to_constant();
        if(result.id()==ID_nil)
        {
          return equals;
        }
        else
        {
          constant_exprt not_value;
          if(result.is_false())
          {
            not_value.make_true();
          }
          else
          {
            not_value.make_false();
          }
          return abstract_object_pointert(
            environment.abstract_object_factory(
              not_value.type(), not_value));
        }
      }
    }
  };

  // Normally if we can't handle an binary operation we would just pass it
  // to a less precise version, but we are the least precise, so we need to
  // implement all the operations.
  // We could always fall back to returning top for the type of the expression
  assert(handlers.find(expr.id())!=handlers.end());

  return handlers[expr.id()](expr);
}

/*******************************************************************\

Function: abstract_objectt::is_top

  Inputs:

 Outputs: Returns true if the abstract object is representing the top (i.e. we
          don't know anything about the value).

 Purpose: Find out if the abstract object is top

\*******************************************************************/

bool abstract_objectt::is_top() const
{
  return top;
}

/*******************************************************************\

Function: abstract_objectt::is_bottom

  Inputs:

 Outputs: Returns true if the abstract object is representing the bottom.

 Purpose: Find out if the abstract object is bottom

\*******************************************************************/

bool abstract_objectt::is_bottom() const
{
  return bottom;
}

/*******************************************************************\

Function: abstract_objectt::to_constant

  Inputs:

 Outputs: Returns true if the abstract object is representing the top (i.e. we
          don't know anything about the value).

 Purpose: If abstract element represents a single value, then that value,
          otherwise nil. E.G. if it is an interval then this will be x if it is
          [x,x] This is the (sort of) dual to the constant_exprt constructor
          that allows an object to be built from a value.

\*******************************************************************/

exprt abstract_objectt::to_constant() const
{
  return nil_exprt();
}

/*******************************************************************\

Function: abstract_objectt::output

  Inputs:
   out - the stream to write to
   ai - ?
   ns - ?

 Outputs:

 Purpose: Print the value of the abstract object

\*******************************************************************/

void abstract_objectt::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns)
{
  if(top)
  {
    out << "TOP";
  }
  else if(bottom)
  {
    out << "BOTTOM";
  }
  else
  {
    out << "Unknown";
  }
}

abstract_object_pointert abstract_objectt::expression_transform_equals_simple(
  const exprt &lhs,
  const exprt &rhs,
  const abstract_environmentt &enviroment) const
{

  abstract_object_pointert lhs_abstract_object=enviroment.eval(lhs);
  abstract_object_pointert rhs_abstract_object=enviroment.eval(rhs);

  const exprt &lhs_value=lhs_abstract_object->to_constant();
  const exprt &rhs_value=rhs_abstract_object->to_constant();

  if(lhs_value.id()==ID_nil || rhs_value.id()==ID_nil)
  {
    // One or both of the values is unknown so therefore we can't conclude
    // whether this is true or false
    return abstract_object_pointert(
      new abstract_objectt(bool_typet(), true, false));
  }
  else
  {
    bool logical_result=lhs_value==rhs_value;
    if(logical_result)
    {
      return abstract_object_pointert(
        new constant_abstract_valuet(true_exprt()));
    }
    else
    {
      return abstract_object_pointert(
        new constant_abstract_valuet(false_exprt()));
    }
  }
}
