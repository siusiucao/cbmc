/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: April 2016

Description: A generic abstract domain that acts as a conventional
             interpreter except for storing abstract domains in the
             environment and mapping from trackable entities
             (variables, arrays, structures, etc.) to storage
             locations allowing write coallescing / array smashing,
             various approaches to pointers, etc.

             Intended as a generic base for non-relational abstractions.

\*******************************************************************/

#ifndef CPROVER_ABSTRACT_ENVIRONMENT_DOMAIN_H
#define CPROVER_ABSTRACT_ENVIRONMENT_DOMAIN_H

#include "ai.h"
#include "abstract_environment.h"


template <class domainT>
class abstract_environment_domaint : public ai_domain_baset, abstract_environmentt
{
 protected :
  bool flow_sensitive;
  
 public:
 abstract_environment_domaint() : flow_sensitivity(false), is_bottom(true) {}
 abstract_environment_domaint(bool fs) : flow_sensitivity(false), is_bottom(true) {}

  // Matters because of sharing_map
  //abstract_environment_domaint(const abstract_environment_domaint &old) {}

  
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);
  
  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;
  
  // no states
  virtual void make_bottom();

  // all states
  virtual void make_top();
  
  // a reasonable entry-point state
  virtual void make_entry();
  
  // This computes the join between "this" and "b".
  // Return true if "this" has changed.
  virtual bool merge(const abstract_environment_domaint &b,
		     locationt from,
		     locationt to);

  // When goto-analyzer-4 is merged will also need
  //  domain_simplify()
  // Which can be implemented in a generic way by recursing
  // and using to_constant and simplify
  
};

#endif
