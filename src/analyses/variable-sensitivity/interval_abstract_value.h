/*******************************************************************\

 Module: analyses variable-sensitivity intervals

 Author: Diffblue Ltd.

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H

#include <iosfwd>

#include <util/interval.h>

#include <analyses/variable-sensitivity/abstract_value.h>
#include <util/std_expr.h>

class interval_abstract_valuet:public abstract_valuet
{
private:
  typedef sharing_ptrt<interval_abstract_valuet>
    interval_abstract_value_pointert;

public:
  explicit interval_abstract_valuet(typet t);
  interval_abstract_valuet(typet t, bool tp, bool bttm);

  interval_abstract_valuet(constant_interval_exprt e, int merge_count);

  explicit interval_abstract_valuet(
    const constant_interval_exprt e);

  interval_abstract_valuet(
    const exprt e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  ~interval_abstract_valuet() override = default;

  virtual exprt to_constant() const override;

  // Interface for transforms
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override;

  virtual void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

protected:
  CLONE
  virtual abstract_object_pointert merge(
    abstract_object_pointert other) const override;

private :
  abstract_object_pointert merge_intervals(
    interval_abstract_value_pointert other) const;

  constant_interval_exprt interval;

  int merge_count;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_INTERVAL_ABSTRACT_VALUE_H
