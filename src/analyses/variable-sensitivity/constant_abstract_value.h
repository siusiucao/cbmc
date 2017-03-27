/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H

#include <iosfwd>

#include <analyses/variable-sensitivity/abstract_value.h>
#include <util/std_expr.h>

class constant_abstract_valuet : public abstract_valuet
{
private:
  typedef sharing_ptrt<constant_abstract_valuet>
    constant_abstract_value_pointert;

public:
  explicit constant_abstract_valuet(typet t);
  constant_abstract_valuet(typet t, bool tp, bool bttm);
  constant_abstract_valuet(const constant_abstract_valuet &old);
  constant_abstract_valuet(
    const exprt e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  CLONE
  MERGE(abstract_valuet)

  virtual exprt to_constant (void) const override;

  virtual void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

protected :
  bool merge_state(
    constant_abstract_value_pointert op1,
    constant_abstract_value_pointert op2);

private :
  exprt value;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_CONSTANT_ABSTRACT_VALUE_H
