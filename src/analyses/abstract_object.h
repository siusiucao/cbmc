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

#include "type.h"
#include "std_expr.h"
#include "std_types.h"

#ifndef CPROVER_ABSTRACT_OBJECT_H
#define CPROVER_ABSTRACT_OBJECT_H

// As we want dynamic dispatch we can't use irepts.
// So we have to do our own reference counting.
// I have no particular preferences over solutions
// Is there an STL (not Boost) C++ reference counted pointer in C++11?
// I'm on a plane so can look it up.
// Anyway, this shoud at least convey the intent

class reference_counted_objectt
{
 private:
  uint64_t counter;
 public :
  reference_counted_objectt() : counter(0) {}
  reference_counted_objectt(const reference_counted_objectt &old) : counter(0) {}

  uint64_t get(void) const { return counter; }
  uint64_t inc(void) { assert(counter != UINT64_T_MAX); return ++counter; }
  uint64_t dec(void) { assert(counter != 0); return --counter; }
};

template<class T>
class reference_counted_pointer
{
 private:
  T * ptr;
  
  void claim (T *p)
  {
    reference_counted_objectt *v = dynamic_cast<reference_counted_object *>(ptr);
    assert(v != NULL);
    v->inc();
    return;
  }

  void release (T *p)
  {
    reference_counted_objectt *v = dynamic_cast<reference_counted_object *>(ptr);
    assert(v != NULL);
    if (v->dec() == 0)
      delete p;
    return;
  }
  
 public :
 reference_counted_pointer(T *p) : ptr(p) { claim(p); }
  
 reference_counted_pointer(const reference_counted_pointer &old) : ptr(old.ptr)
 {
   claim(p);
 }

 reference_counted_pointer & operator= (const reference_counted_pointer &op)
 {
   claim(op.ptr);   // Order matters!
   release(this->ptr);
   this->ptr = op.ptr;

   return (*this);
 }
   
 virtual ~reference_counted_pointer () { release(this->ptr); }

 T * operator T* (void) { return this->ptr; }
 const T * operator T* (void) const { return this->ptr; }
}



// Now we need abstract objects to represent the possible values that
// the environment stores.

// The top of the heirarchy is something that can only be top or bottom
// but can represent any type of object.
// The interface is deliberately similar to ai_base but it does not
// inherit from it as this is an abstraction of one object rather than
// the full state of the program at an instruction.
// Also note that these objects are intended to be immutable, hence the
// slight difference in interface;

// I think there is a pattern for this but for now this will do
#define CLONE(T) virtual abstract_objectt * clone () const { return new T(*this); }


class abstract_objectt : public reference_counted_objectt
{
 protected :
  typet type;
  bool top;
  bool bottom;

  
 public :
  abstract_objectt (typet t) : type(t), is_top(true), is_bottom(false) {}
  abstract_objectt (typet t, bool tp, bool bttm) : type(t), top(tp), bttm(bttm) { assert(!(top && bottom)); }
  abstract_objectt (const abstract_object &old) : type(old.type), top(old.top), bottom(old.bottom) {}

  CLONE(abstract_objectt)
  
  typet type(void) const {return type;};
  abstract_object * merge(const abstract_object &op)
  {
    // Double dynamic dispatch deleriously desired!
  }
  virtual bool is_top() { return top; }
  virtual bool is_bottom() { return bottom; }

  // if abstract element represents a single value, then that value, otherwise nil
  // E.G. if it is an interval then this will return true if it is [x,x]
  virtual exprt to_constant (void) const { return false; }
};


// Methods that use this should go into abstract_object.cpp
class abstract_environmentt;


// We have classes for each predefined type (types.h).
// These add functionality to the interface but are still top/bottom
// I.E. full insensitivity
// We inherit from these to add sensitivity.
// Note that abstract_boolean is used by the environment to evaluate logical conditions
// abstract_integer is used some of the more sensitive abstract_arrays

class abstract_valuet : public abstract_objectt
{
  // All the usual stuff
  CLONE(abstract_valuet);
}
  
class abstract_booleant : public abstract_valuet
{
  // All the usual stuff
  CLONE(abstract_booleant);
}

class abstract_integert : public abstract_objectt
{
  // All the usual stuff
  CLONE(abstract_integert);
}

class abstract_floatt : public abstract_objectt
{
  // All the usual stuff
  CLONE(abstract_floatt);
}

class abstract_arrayt : public abstract_objectt {
  // All the usual stuff
  CLONE(abstract_arrayt);
  
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

class full_abstract_booleant : public abstract_booleant
{
  // Track true and false as well as top
  // to_constant matters for Boolean operations
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
