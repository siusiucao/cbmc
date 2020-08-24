/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>
#include <stack>

class abstract_environmentt;
class index_exprt;

class array_abstract_objectt : public abstract_objectt
{
public:
  explicit array_abstract_objectt(const typet &type);
  array_abstract_objectt(const typet &type, bool top, bool bottom);
  explicit array_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  virtual abstract_object_pointert read(
    const abstract_environmentt &env,
    const exprt &specifier,
    const namespacet &ns) const override;

  virtual abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const exprt &specifier,
    const abstract_object_pointert value,
    bool merging_write) const override;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

protected:
  CLONE

  virtual abstract_object_pointert read_index(
    const abstract_environmentt &env,
    const index_exprt &index,
    const namespacet &ns) const;

  virtual sharing_ptrt<array_abstract_objectt> write_index(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const index_exprt &index_expr,
    const abstract_object_pointert value,
    bool merging_write) const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H
