/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H

class typet;
class constant_exprt;

#include <util/expr.h>
#include <memory>


#define CLONE \
  virtual abstract_objectt* clone() const \
  { \
    typedef std::remove_const<std::remove_reference<decltype(*this)>::type \
      >::type current_typet; \
    return new current_typet(*this); \
  } \

typedef std::shared_ptr<class abstract_objectt> abstract_object_pointert;

class abstract_objectt
{
public:
  abstract_objectt(const typet &type);
  abstract_objectt(const typet &type, bool top, bool bottom);
  abstract_objectt(const abstract_objectt &old);
  abstract_objectt(const constant_exprt &expr);

  const typet &get_type() const;
  virtual bool is_top() const;
  virtual bool is_bottom() const;

  // Sets the state of this object
  virtual void merge_state(
    const abstract_object_pointert op1, const abstract_object_pointert op2);

  // This is both the interface and the base case of the recursion
  // It uses merge state to
  virtual abstract_object_pointert merge(
    const abstract_object_pointert op);

  virtual exprt to_constant (void) const;

  virtual void output(
    std::ostream &out, const class ai_baset &ai, const class namespacet &ns);

  CLONE

protected :
  typet type;
  bool top;
  bool bottom;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
