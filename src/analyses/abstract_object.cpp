/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: December 2016

Description: Implementation of the single value abstractions.

\*******************************************************************/

#include "abstract_object.h"

abstract_objectt *abstract_arrayt::read_index(const abstract_environemnt &env, exprt index) const {
  return (env.env.is_def(*this)) ? env.env(*this) : top;
}

abstract_objectt *element_arrayt::read_index(const abstract_environemnt &env, exprt index) const {
  abstract_object abs(env.eval(index));
  abstract_integert index_value(to_abstract_integert(abs));
  mp_integer value;
  
  if (index_value.to_integer(&value))
  {
    // Fast path if it is a single value
  }
  else
  {
    for (/* stored values */) {
      // Compute the meet of all possible values

    }

    return meet;
  }
}

abstract_objectt *abstract_pointert::dereference(const abstract_environment &env) const {
  return env.abstract_object_factory(this->type().base()); // Top
}

abstract_objectt *single_pointert::dereference(const abstract_environment &env) const {
  if (is_top())
    return abstract_pointer::dereference(env);
  else if (is_bottom())
    // ...
  else
    return env.eval(target());
}

abstract_objectt *pointer_sett::dereference(const abstract_environment &env) const {
  if (is_top())
    return abstract_pointer::dereference(env);
  else if (is_bottom())
    // ...
  else if (values.size() == 1)
    return env.eval(value[0]);
  else
    for (v : values)
      merge(env.eval(v));
}

