/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: December 2016

Description: Abstractions of single variables.  The key feature is
             run-time (via dynamic dispatch) delegation of the level
             of sensitivity of pointers, arrays, structures, unions
             and values.

             This code generally assumes that the program will be type
             safe.  It aims to be correct in the type unsafe case but
             (very) overapproximate.

\*******************************************************************/

#include <assert.h>
#include <memory>

#include <util/type.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "abstract_environment.h"


#ifndef CPROVER_ABSTRACT_OBJECT_H
#define CPROVER_ABSTRACT_OBJECT_H




// We need abstract objects to represent the possible values that
// the environment stores, i.e. abstractions of single variables.

// The type heirarchy here is intended to capture the range of possible
// abstractions, with a subclass representing a more precise / refined
// abstraction (although the converse is not necessarily true, just because
// intervals are more precise than constants does not mean they have to
// inherit) from them.  Some of the objects are only suitable for certain
// types of variables (i.e. it would be strange to use an array abstraction
// to track a single float variable).
// *. The type() field tracks the type of variable / expression that is being
//    abstracted.
// *. The run-time type of the object used is the kind of abstraction used.


// The top of the heirarchy is something that can only be top or bottom
// but can represent any type of variable.
// The interface is deliberately similar to ai_base but it does not
// inherit from it as this is an abstraction of one object rather than
// the full state of the program at an instruction.
// Also note that these objects are intended to be immutable to improve sharing,
// hence the slight difference in interface;

// I think there is a pattern for this but for now this will do
#define CLONE virtual abstract_objectt * clone() const { return new typeof(*this)(*this); }

// Merge constructs an object of the most specific parent type of two objects.
// Thus we can merge different abstractions of the same object.
// This allows fine grain choice of abstractions without forcing all variables
// of one type to use the same abstraction, or even the same variable in
// different places can use different abstractions.
#define MERGE(parent_typet) virtual abstract_objectt * merge(const abstract_object *op) const \
  {								\
    assert(this->type==op->type);				\
    typedef current_type typeof(*this);                         \
    current_type(this) n = dynamic_cast<current_type>(op);      \
    if (n != NULL)                               		\
    {								\
      m = new current_type(this->type);                         \
      m->merge_state(this, op);                                 \
    }                                                           \
    else                                                        \
    {                                                           \
      return parent_typet::merge(*op);                          \
    }                                                           \
}


class abstract_objectt
{
 protected :
  typet type;
  bool top;
  bool bottom;

  // Sets the state of this object
  virtual void merge_state (abstract_objectt *op1, abstract_objectt *op2) const
  {
    top=op1->top||op2->top;
    bottom=op1->bottom && op2->bottom;
    assert(!(top && bottom));
    return;
  }
  
 public :
  abstract_objectt (typet t) : type(t), top(true), bottom(false) {}
  abstract_objectt (typet t, bool tp, bool bttm) : type(t), top(tp), bttm(bttm) { assert(!(top && bottom)); }
  abstract_objectt (const abstract_object &old) : type(old.type), top(old.top), bottom(old.bottom) {}
  abstract_objectt (const constant_exprt e) : type(e.type()), top(true), bottom(false) {}
  
  CLONE
  
  typet type(void) const {return type;};

  // This is both the interface and the base case of the recursion
  // It uses merge state to 
  virtual abstract_object * merge(const abstract_object *op) const
  {
    assert(this->type==op->type);
    abstract_objectt *m=new current_type(*this);
    m->merge_state(this, op);
    return m;
  }
  virtual bool is_top() { return top; }
  virtual bool is_bottom() { return bottom; }

  // If abstract element represents a single value, then that value, otherwise nil
  // E.G. if it is an interval then this will x if it is [x,x]
  // This is the (sort of) dual to the constant_exprt constructor that allows an object
  // to be built from a value.
  virtual exprt to_constant (void) const { return nil_expr(); }
};


// Methods that use this should go into abstract_object.cpp
class abstract_environmentt;


// We have classes for each CPROVER type (types.h).
// These add functionality to the interface but are still top/bottom
// I.E. full insensitivity
// We inherit from these to add sensitivity.
// Note that abstract_boolean is used by the environment to evaluate logical conditions
// abstract_integer is used some of the more sensitive abstract_arrays

class abstract_valuet : public abstract_objectt
{
 public :
  abstract_valuet(typet t) : abstract_objectt(t) {}
  abstract_valuet(typet t, bool tp, bool bttm) : abstract_objectt(t, tp, bttm) {}
  abstract_valuet(const abstract_valuet &old) : abstract_objectt(old) {}
  abstract_valuet(const constant_exprt e) : type(e.type()), top(true), bottom(false) {}

  CLONE
  MERGE(abstract_objectt)
}
  

class abstract_arrayt : public abstract_objectt {
 public :
  abstract_arrayt(typet t) : abstract_objectt(t)
  {
    assert(t.id() == ID_array);  // Only a meaningful abstraction for arrays
  }
  abstract_arrayt(typet t, bool tp, bool bttm) : abstract_objectt(t, tp, bttm)
  {
    assert(t.id() == ID_array); 
  }
  abstract_arrayt(const abstract_arrayt &old) : abstract_objectt(old)
  {
    assert(t.id() == ID_array); 
  }
  abstract_arrayt(const constant_exprt e) : type(e.type()), top(true), bottom(false)
  {
    assert(t.id() == ID_array); 
  }


  CLONE
  MERGE(abstract_objectt)
  
  virtual abstract_objectt * read_index(const abstract_environment &env, const exprt index) const
  {
    array_typet at(to_array_type(type()));
    return env.abstract_object_factory(at.subtype(), is_top()); 
  }
  
  virtual abstract_object * write_index(abstract_environment &env, const std::stack<exprt> access_path, const abstract_objectt *value, bool merging_write)
  {
    assert(!access_path.empty());
    assert(access_path.top().id() == ID_index);
    
    if ((is_top() && (value.is_top())) ||
	(is_bottom() && (value.is_bottom())))
      return this;
    else
      return env.abstract_object_factory(type(), true);
  }
};

class abstract_structt : public abstract_objectt
{
  // All the usual stuff
  CLONE(abstract_structt);
  
  virtual abstract_object * read_member(const abstract_environment &end, const irep_idt component_name) const
  {
    // As above, return top or bottom of component type
  }

  virtual abstract_object * write_member(abstract_environment &env, const std::stack<exprt> access_path, const abstract_objectt *value, bool merged_write)
  {
    // As above
  }
}

class abstract_uniont : public abstract_objectt
{
    // All the usual stuff
  CLONE(abstract_uniont);
  
  virtual abstract_object * read_member(const abstract_environment &end, const irep_idt component_name) const
  {
    // As above, return top or bottom of component type
  }

  virtual abstract_object * write_member(abstract_environment &env, const std::stack<exprt> access_path, const abstract_objectt *value, bool merged_write)
  {
    // As above
  }
}

class abstract_pointert : public abstract_objectt {
  // All the usual stuff
  CLONE(abstract_pointert);
  
  virtual abstract_objectt * read_dereference(const abstract_environemnt &env) const
  {
    // Return top/bottom of the appropriate type.
  }

  virtual abstract_objectt * write_dereference(const abstract_environemnt &env, const std::stack<exprt> access_path, const abstract_objectt *value, bool merged_write) const
  {
    env.havoc("Write to base abstract_pointert");
    // Pointers are now sound, just overapproximate...
  }
}


// Right that's all of the boring interface out of the way
// Now we can get on to abstract_objects that actually *do* something.
// Unlike irepts, these can (and should) add fields but keep the same interface
// Use sharing_maps and reference_counted_pointers where at all possible.

// Note that none of these are urgent as the rest of the framework and
// are mostly here as note-taking and to illuminate various other components

// to_constant methods are useful for these as they help increase the precision



// This is a constant abstraction for values.  It could be used for structures,
// arrays. etc. but it's a better bet to use a precise abstraction for these but
// use constant abstractions for the contents
class constant_abstractiont : public abstract_valuet
{
 protected :
  constant_expr value;

    // As this object adds state, it needs a merge state
  virtual void merge_state (constant_abstractiont *op1, constant_abstractiont *op2) const
  {
    abstract_objectt::merge_state(op1, op2);
    if (!top && !bottom)
    {
      if (op1->value==op2->value)
	this->value=op1->value;
      else
      {
	this->top=true;
	assert(this->bottom==false);
	this->value=get_nil_irep();
      }
    }
    return;
  }

  
 public :
 constant_abstractiont(typet t) : abstract_objectt(t), value(get_nil_irep()) {}
 constant_abstractiont(typet t, bool tp, bool bttm) : abstract_objectt(t, tp, bttm), value(get_nil_irep()) {}
 constant_abstractiont(const constant_abstractiont &old) : abstract_objectt(old), value(old.value) {}
 constant_abstractiont(const constant_exprt e) : type(e.type()), top(false), bottom(false), value(e) {}

  CLONE
  MERGE(abstract_objectt)

  virtual constant_exprt to_constant (void) const { return this->value; }
  
}



class smash_arrayt : public abstract_array
{
  // Store a single abstract domain element, all write go to this and are
  // merged_writes
}

class element_arrayt : public abstract_arrayt
{
  // Store an abstract domain per array element
  // (when they are not top -- sharing_map)
  // Eval the index (this is why you need the abstract_environment
  // to_constant to get an exact index
  // otherwise, a merged write to all
  // If you want a later version can detect when the index evaluated to an interval
  // and only update those locations in the array
}

class write_sequence_arrayt : public abstract_arrayt
{
  // The other way of doing it -- really non-urgent
  // Almost symbolic, store a sequence of updates along with the abstract domains
  // for their write indexes.
  // Any read then checks whether the abstract domain of it's index overlaps with
  // any of them and if so then merge the written element
  // Effectively lazy resolution of writes
}


class field_sensitive_structt : public abstract_structt
{
  // A sharing_map of the members that have been written to (and are not top)
}


class single_value_uniont : public abstract_uniont
{
  // Keeps track of the last member accessed and keeps a (single) abstract
  // domain for that, read or writes to others give top (and change the tracked member)
}


class lower_havoc_pointer :  public abstract_pointert
{
  // Just havoc the appropriate type
}

class single_pointert : public abstract_pointert
{
  // Track a single pointer; to_constant really matters for simplification here
  // we will need this
}

class pointer_sett : public abstract_pointert
{
  // We might need one of these, a simple set would do for now
}

class value_sett : public abstract_pointert
{
  // Connect to the existing value_set analysis
  // This has a *lot* of the smarts and weird edge cases around pointer arithmetic
  // It's better to use this than try to rebuild all of it
  // Maybe in the long-term we should port the value_set analysis to this framework
}

#endif
