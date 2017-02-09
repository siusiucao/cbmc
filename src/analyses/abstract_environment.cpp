/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: April 2016

Description: An environment which stores abstract objects.  For use in
             non-relational abstract domains.  Where possible things
             with value top are not stored to give a more compact
             representation.

\*******************************************************************/

#include "abstract_environment.h"

#include "abstract_object.h"



abstract_objectt abstract_environmentt::eval(const exprt &e) const {
  switch(e.id()) {
  case ID_symbol : 
    return (map.is_def(e)) ? env(e) : abstract_object_factory(e.type(), true);
    break;
    
  case ID_index :
  {
    index_exprt i(to_index_exprt(e));
    abstract_objectt abs(eval(e.array()));
    abstract_arrayt abs_array(to_abstract_arrayt(abs));
    return abs_array.read_index(*this, e.index());
  }
  break;

  case ID_member :
    // Similar
    break;
  
  case ID_dereference :
  {
    dereference_exprt d(to_dereference_exprt(e));
    abstract_objectt abs(eval(e.pointer()));
    abstract_pointert abs_pointer(to_abstract_pointert(abs));
    
    return abs_pointer.dereference(*this);
  }
  break;
  
  case ID_address_of : // Needs special handling
    return abstract_object_factory(e.type(), e);
    break;

  case ID_and :
  case ID_or :
  case ID_not :
    // and so on...
    return eval_boolean(e.id());
    break;
   
    
  // All of the domain specific stuff
  default :
    return eval_rest(e);
    break;
  }

  assert(0);
}


abstract_object *abstract_environment::eval_logical(const exprt &e) const {
  // Should be evaluable just using abstract_booleant
}
  
// Fall back over-approximation.
abstract_objectt *abstract_environment::eval_rest(const exprt &e) const {
  return abstract_object_factory(e.type(), true);
}





bool abstract_environment::assign(const exprt &e, const abstract_objectt *d) {
  exprt s = e;
  std::stack<exprt> stactions;    // I'm not a continuation, honest guv'
  
  while (s.id() != ID_symbol)
  {
    if (s.id() == ID_index || s.id() == ID_member || s.id() == ID_derefence)
    {
      stactions.push(s);
      s = s.op();
    }
    else if (s.id() == ID_dereference)
    {
      // LOL, nope!
    }
    else
    {
      // Attempting to assign to something unreasonable
      // Your goto-program is broken
      die_horribly();
    }
  }

  
  abstract_objectt *write_value = d;

  if (!stactions.empty())
  {
    // Delegate the continuation^W writing
    switch (s.type().id())
    {
    case ID_struct :
    {
      abstract_structt *str = NULL;
      if (map.is_def(s))
	str = map.find();
      else
	str = abstract_object_factory(s.type(), true);

      d = str.write_member(*this, staction, write_value, false);
    }

    case ID_array :
    {
      abstract_arrayt *str = NULL;
      if (map.is_def(s))
	str = map.find();
      else
	str = abstract_object_factory(s.type(), true);

      d = str.write_index(*this, staction, write_value, false);
    }

    // ... and so on ...
    }
  }

  if (d->is_top())
  {
    env.erase(s);
    destroy(d); // well, decrement reference count and thus ...
  }
  else
  {
    env.update(s, d);
  }
}


// This is the most generic implementation I can come up with
// Actual domains should implement this in a more sane way.
bool abstract_environment::assume (const exprt &e)
{
  abstract_objectt *res = eval(e);
  abstract_booleant *b = dynamic_cast<abstract_booleant>(res);

  assert(b != NULL);

  if (b->to_constant().is_false())
  {
    make_bottom();
    return true;
  }
  else
    return false;
}


 virtual bool merge (const abstract_environmentt &env)
 {
   // Use the sharing_map's "iterative over all differences" functionality
   // This should give a significant performance boost
   // We can strip down to just the things that are in both
 }

