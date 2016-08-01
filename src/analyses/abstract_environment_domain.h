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

typedef std::set<exprt> expression_sett;
  

template <class domainT>
class abstract_environment_domaint : public virtual ai_domain_baset
{
  /*** Environment part ***/
 public :
  
  // Is this an expression that can be tracked
  virtual bool trackable(const exprt &e) const;

  // Is it tracked
  virtual bool is_tracked(const exprt &e) const;
  virtual void track(const exprt &e, bool concrete_location = true);
  virtual void untrack(const exprt &e);

  // Access
  domainT read(const exprt &e) const;
  void write(const exprt &e, const domainT &d);

 protected:
  template <class abs_domainT>
  struct _abstract_cellt {
    abs_domainT element;
    bool concrete_location;

    _abstract_cellt (const abs_domainT &e, const bool c) : element(e, c) {}
    
  };

  typedef struct _abstract_cellt<domainT> abstract_cellt; 
  typedef std::map<exprt, abstract_cellt> mapt;
  mapt dom;

  // Implements the mapping from expression to zero or more entries in
  // the map
  virtual expression_sett lookup(const exprt &e) const;
  virtual expression_sett lookup_symbol(const exprt &e) const;
  virtual expression_sett lookup_array(const exprt &e) const;
  virtual expression_sett lookup_structure(const exprt &e) const;
  virtual expression_sett lookup_union(const exprt &e) const;
  virtual expression_sett lookup_dereference(const exprt &e) const;
  virtual expression_sett lookup_rest(const exprt &e) const;


  /*** Abstract domain part ***/
 public:

  // Domain interface
 abstract_environment_domaint() {}
  
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

 protected:
  virtual domainT eval (const exprt &e) = 0;
  virtual void assume (const exprt &e);
  
};


#endif
