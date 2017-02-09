/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: April 2016

Description: An environment which stores abstract objects.  For use in
             non-relational abstract domains.  Where possible things
             with value top are not stored to give a more compact
             representation.

\*******************************************************************/

#include <assert.h>


#ifndef CPROVER_ABSTRACT_ENVIRONMENT_H
#define CPROVER_ABSTRACT_ENVIRONMENT_H

// Forwards defintion
class abstract_objectt;

// These are mutable, unlike abstract_objects
class abstract_environmentt {
 protected :
  sharing_map<symbol_exprt, reference_counted_pointer<abstract_object> > map;

  // Needs a 'top' and 'bottom' as well
  
 public :
  // The copy constructor matters because of the sharing_map

  
  // This is an interface to a "policy" that should be run-time
  // configurable.  So that command line flags such as:
  //  --array-sensitivity=smash
  // affect what types are produced by these factories.
  // Implement as you see fit.
  virtual abstract_objectt *abstract_object_factory (const typet t, bool top = true);

  // For converting constants in the program
  // Maybe these two should be compacted to one call...
  virtual abstract_objectt *abstract_object_factory (const typet t, const constant_exprt e);
  

  // These three are really the heart of the method
  virtual abstract_objectt *eval(const exprt &e) const;
  virtual bool assign(const exprt &e, const abstract_objectt *d);
  virtual bool assume (const exprt &e) {  /* eval, if false then bottom */}

  
  virtual bool merge (const abstract_environmentt &env);

  // This should be used as a default case / everything else has failed
  // The string is so that I can easily find and diagnose cases where this occurs
  virtual void havoc (std::string) { make_top(); }

  // For the less havocy pointer we might need this, which can be applied
  // eagerly or lazily
  //virtual void havoc (std::string s, typet t);

 protected : 

  // We may need to break out more of these cases into these
  virtual abstract_object *eval_logical(const exprt &e) const;
  
  // Hook for domain specific handling of operators
  virtual abstract_objectt *eval_rest(const exprt &e) const;
    
}


#endif
