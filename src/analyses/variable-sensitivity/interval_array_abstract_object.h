/*******************************************************************\

Module: analyses variable-sensitivity interval-values arrays

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef PROJECT_INTERVAL_ARRAY_ABSTRACT_OBJECTT_H
#define PROJECT_INTERVAL_ARRAY_ABSTRACT_OBJECTT_H

#include "constant_array_abstract_object.h"

class interval_array_abstract_objectt : public constant_array_abstract_objectt
{
public:
  explicit interval_array_abstract_objectt(typet type);

  interval_array_abstract_objectt(typet type, bool top, bool bottom);

  interval_array_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

protected:
  CLONE
  abstract_object_pointert read_index(
    const abstract_environmentt &env,
    const index_exprt &index,
    const namespacet &ns) const override;

  sharing_ptrt<array_abstract_objectt> write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const index_exprt &index_expr,
    const abstract_object_pointert value,
    bool merging_write) const override;

  bool eval_index(
    const index_exprt &index,
    const abstract_environmentt &env,
    const namespacet &ns,
    mp_integer &out_index) const override;

public:
  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;
};

#endif //PROJECT_INTERVAL_ARRAY_ABSTRACT_OBJECTT_H
