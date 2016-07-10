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

\*******************************************************************/

#ifndef CPROVER_MAP_DOMAIN_H
#define CPROVER_MAP_DOMAIN_H

#include "ai.h"

template<class domainT>
class abstract_environmentt
{
 public :
  
  // Is this an expression that can be tracked
  virtual bool trackable(const expr &e) const;

  // Is it tracked
  bool is_tracked(const expr &e) const;
  void track(const expr &e);

  // Access
  domainT read(const expr &e) const;
  void write(const expr &e, const domainT & d);

 protected:
  typedef std::map<exprt, domainT> mapt;

  mapt dom;

  // Implements the mapping from expression to zero or more entries in
  // the map
  virtual std::set<exprt> lookup(const exprt &t);
  virtual std::set<exprt> lookup_symbol(const exprt &t);
  virtual std::set<exprt> lookup_array(const exprt &t);
  virtual std::set<exprt> lookup_structure(const exprt &t);
  virtual std::set<exprt> lookup_union(const exprt &t);
  virtual std::set<exprt> lookup_dereference(const exprt &t);
  virtual std::set<exprt> lookup_rest(const exprt &t);

};


template<class domainT>
class abstract_enivornment_domaint:public ai_domain_baset, abstract_environmentt<domainT>
{
 public:

  // Domain interface
  abstract_enivornment_domaint() {}
  
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
  bool merge(const abstract_enivornment_domaint &b,
	     locationt from,
	     locationt to);
  
};

//typedef ait<abstract_enivornment_domaint> map_ait;

#endif
