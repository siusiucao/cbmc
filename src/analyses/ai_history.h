/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Abstract Interpretation history

#ifndef CPROVER_ANALYSES_AI_HISTORY_H
#define CPROVER_ANALYSES_AI_HISTORY_H

#include <goto-programs/goto_model.h>

#define IMPLIES(X,Y) (!((X)) || ((Y)))


/// This is the base of tracking location and / or context in the
/// abstract interpretter.  It stores an abstraction / representation of
/// the history of the control-flow of the program.
class ai_history_baset {
public:
  typedef goto_programt::const_targett locationt;
  typedef irep_idt function_namet;

  ai_history_baset(const ai_history_baset &) {}
  
  /// Create a new history starting from a given location
  /// PRECONDITION(l.is_dereferenceable());
  explicit ai_history_baset(locationt) {}

  /// Move from current location to "to"
  /// may merge with existing histories at that point
  /// PRECONDITION(to.id_dereferenceable());
  /// PRECONDITION(to \in goto_program.get_successors(current_location()) ||
  ///              current_location()->is_function_call() ||
  ///              current_location()->is_end_function());
  // const historyT * step(locationt to, std::set<historyT> &others) const;
  // Like merge : needs the actual types
  /// POSTCONDITION(result is a pointer to an element in others or nullptr)

  /// The order of the working set
  // bool operator < (const historyT &op) const;
 

  /// The most recent location in the history
  /// POSTCONDITION(return value is dereferenceable)
  virtual const locationt & current_location(void) const = 0;

  /// History objects should be comparable
  virtual bool operator==(const ai_history_baset &) const = 0;  


  /// Domains with a substantial height may need to widen when merging
  /// this method allows the history to provide a hint on when to do this
  virtual bool widen(const ai_history_baset &other) const
  {
    return false;
  }

};


/// The common case of history is to only care about where you are now,
/// not how you got there!
/// Invariants are not checkable due to C++...
class ahistoricalt : public ai_history_baset {
private:
  // DATA_INVARIANT(current.is_dereferenceable(), "Must not be _::end()")
  locationt current;

  ahistoricalt(locationt i) :
   ai_history_baset(i),
   current(i)
  {}

public:
  ahistoricalt(const ahistoricalt &old) :
   ai_history_baset(old),
   current(old.current)
  {}

  ahistoricalt(const history_optionst &op, locationt i) :
    ai_history_baset(op, i),
    current(i)
  {}
  
  const ahistoricalt * step(locationt to, std::set<ahistoricalt> &others) const
  {
    ahistoricalt next(to);
    
    if (others.empty())
    {
      const auto r=others.insert(next);
      return &(*(r.first));
    }
    else
    {
      // Aggressively merge histories because -- why not?
      INVARIANT(others.size() == 1, "Only needs one history per location");

      const auto it=others.begin();
      INVARIANT(*(it) == next,
                "The next location in history map must contain next history");

      return &(*it);
    }
  }

  bool operator < (const ahistoricalt &op) const
  {
    return this->current_location()->location_number <
      op.current_location()->location_number;
  }
  
  const locationt & current_location(void) const override
  {
    return current;
  }

  bool operator==(const ai_history_baset &op) const override
  {
    // It would be nice to:
    //  return this->current == op.current
    // But they may point to different goto_programs, giving undefined behaviour in C++
    // So (safe due to data invariant & uniqueness of location numbers) ...
    return this->current_location()->location_number ==
      op.current_location()->location_number;
  }

  // Use default widening
  // without history there is no reason to say any location is better than
  // another to widen.

  #warning "history needs output"
};


/// TODO class call_stack_historyt : public ai_history_baset { ... }
/// TODO class calling_context_historyt : public ai_history_baset { ... }

#undef IMPLIES
 
#endif // CPROVER_ANALYSES_AI_HISTORY_H

