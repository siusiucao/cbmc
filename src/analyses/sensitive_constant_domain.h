/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: January 2017

Description: An example of using the abstract domain infrastructure

\*******************************************************************/

#include "abstract_environment_domain.h"

#ifndef CPROVER_SENSITIVE_CONSTANT_DOMAIN_H
#define CPROVER_SENSITIVE_CONSTANT_DOMAIN_H

// All we should need is...

class integer_constant : public abstract_integert
{
 protected :
  constant_exprt value;
 public :
  // Just need merge
}

class float_constant : public abstract_floatt
{
 protected :
  constant_exprt value;
 public :
  // Just need merge
}


class sensitive_constant_domain : public abstract_environment_domain
{
  virtual abstract_objectt *eval_rest(const exprt &e) const
  {
    // Just have to implement transformers
    // In this case, evaluate left and right
    // if they both give meaningful is_constant() then substitue and simplify
  }
}  

#endif
