/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_CONSTANT_PROPAGATOR_H
#define CPROVER_CONSTANT_PROPAGATOR_H

#include <iostream>

#include "ai.h"

#include "replace_symbol_ext.h"

class constant_propagator_domaint:public ai_domain_baset
{
public:
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai_base,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai_base,
    const namespacet &ns) const;

  bool merge(
    const constant_propagator_domaint &other,
    locationt from,
    locationt to);

  virtual exprt domain_simplify(
    const exprt &condition,
    const namespacet &ns,
    const bool lhs=false) const;

  virtual void make_bottom()
  {
    values.set_to_bottom();
  }

  virtual void make_top()
  {
    values.set_to_top();
  }

  virtual void make_entry()
  {
    make_top();
  }

  struct valuest
  {
  public:
    valuest():is_bottom(true) {}
    
    // maps variables to constants
    replace_symbol_extt replace_const;
    bool is_bottom;
    
    bool merge(const valuest &src);
    bool meet(const valuest &src);
    
    // set whole state

    inline void set_to_bottom()
    {
      replace_const.clear();
      is_bottom=true;
    }
    
    inline void set_to_top()
    {
      replace_const.clear();
      is_bottom=false;
    }

    // set single identifier

    inline void set_to(const irep_idt &lhs, const exprt &rhs)
    {
      replace_const.expr_map[lhs]=rhs;
      is_bottom=false;
    }

    inline void set_to(const symbol_exprt &lhs, const exprt &rhs)
    {
      set_to(lhs.get_identifier(), rhs);
    }

    inline bool set_to_top(const symbol_exprt &expr)
    {
      return set_to_top(expr.get_identifier());
    }

    bool set_to_top(const irep_idt &id);

    bool is_constant(const exprt &expr) const;
    bool is_array_constant(const exprt &expr) const;
    bool is_constant_address_of(const exprt &expr) const;

    bool is_empty() const
    {
      assert(replace_const.type_map.empty());
      return replace_const.expr_map.empty();
    }

    void output(std::ostream &out, const namespacet &ns) const;
  };

  valuest values;

protected:
  void assign_rec(
    valuest &values,
    const exprt &lhs, const exprt &rhs,
    const namespacet &ns);

  bool two_way_propagate_rec(
    const exprt &expr,
    const namespacet &ns);
};

class constant_propagator_ait:public ait<constant_propagator_domaint>
{
public:
  constant_propagator_ait(
    goto_functionst &goto_functions,
    const namespacet &ns)
  {
    operator()(goto_functions, ns);
    replace(goto_functions, ns);
  }

  constant_propagator_ait(
    goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    operator()(goto_function, ns);
    replace(goto_function, ns);
  }

protected:
  friend class constant_propagator_domaint;

  void replace_array_symbol(
		  exprt &expr);

  void replace(
    goto_functionst::goto_functiont &,
    const namespacet &);

  void replace(
    goto_functionst &,
    const namespacet &);

  void replace_types_rec(
    const replace_symbolt &replace_const, 
    exprt &expr);

};

#endif
