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


/// This is for passsing configuration options to history objects
/// The default one has no options.
class ai_history_base_optionst
{
  ai_history_base_optionst ()
  {
  }
}


/// This is the base of tracking location and / or context in the
/// abstract interpretter.  It stores an abstraction / representation of
/// the history of the control-flow of the program.
/// It has a number of different roles ...
class ai_history_baset {
public:
  typedef ai_history_base_optionst history_optionst;
  typedef goto_programt::const_targett locationt;
  typedef irep_idt function_namet;

  ai_history_baset(const ai_history_baset &) {}

  
  /// [1]. To track work to be done via ai_baset's work-queue.
  
  /// Create a new history starting from a given location
  /// PRECONDITION(l.is_dereferenceable());
  explicit ai_history_baset(const history_optionst &, locationt) {}

  /// Move from "from" to "to"
  /// PRECONDITION(to.id_dereferenceable());
  /// PRECONDITION(to \in goto_program.get_successors(current_location()))
  virtual void step(locationt to) = 0;
  // Maybe ai_historical_baset(const ai_history_baset &old, locationt next)?
  #warning "Make an actual decision over whether ai_history_baset is functional or not!"


  
  /// [2]. To index the storage of domains.

  /// For use in hash tables
  virtual size_t storage_hash(void) const = 0;
  
  /// It is sometimes useful to ignore some of the details of the history.
  /// For example if you want to store one domain per function
  /// (i.e. location insensitive) you want the history to track the location
  /// but to discard it when looking up the appropriate domain.
  virtual bool storage_equivalent(const ai_history_baset &op) const
  {
    bool return_value = (*this == op);

    /// General properties of this method
    /// All implementations must meet these!
    INVARIANT(IMPLIES((*this == op), return_value == true));
    INVARIANT(IMPLIES(return_value == true,
                      this->storage_hash() == op.storage_hash()));

    return return_value;
  }

  static size_t hash (const ai_history_baset &h)
  {
    return h.storage_hash();
  }

  static bool equal(const ai_history_baset &h, const ai_history_baset &k)
  {
    return h.storage_equivalent(k);
  }


 
 
  /// [3]. To tell which instructions to approximate in the transformers
  ///      and to indentify which successor / branch has been taken.
  
  /// The most recent location in the history
  /// POSTCONDITION(return value is dereferenceable)
  virtual const locationt & current_location(void) const = 0;

  /// History objects should be comparable
  virtual bool operator==(const ai_history_baset &) const = 0;  


 
  
  /// [4]. To hint to domains, on merge, when to widen.

  /// Domains with a substantial height may need to widen when merging
  /// this method allows the history to provide a hint on when to do this
  virtual bool widen(const ai_history_baset &other) const
  {
    return false;
  }


#if 0  
  #warning "haven't decided if we need this or not yet"
  /// For backwards compatability allow implicit casts to locationt
  operator const locationt &(void) const
  {
    return current_instruction_location();
  }
#endif
}


/// The common case of history is to only care about where you are now,
/// not how you got there!
/// Invariants are not checkable due to C++...
class ahistoricalt : public ai_history_baset {
private:
  // DATA_INVARIANT(current.is_dereferenceable(), "Must not be _::end()")
  locationt current;

public:
  ahistoricalt(const ahistoricalt &old) : current(old.current) {}

  /// [1]. Work queue
  ahistoricalt(const history_optionst &, locationt i) : current(i) {}
  void step(locationt to) override
  {
    current = to;
    return;
  }

 
  /// [2]. Storage modulo ...
  virtual size_t storage_hash(void) const override
  {
    // Safe due to data invariant
    return this->current.location_number;
  }

  // Use default storage equivalence


  /// [3]. Transformer interface
  const locationt & current_instruction_location(void) const override
  {
    return current;
  }

  bool operator==(const ahistoricalt &op) const override
  {
    // It would be nice to:
    //  return this->current == op.current
    // But they may point to different goto_programs, giving undefined behaviour in C++
    // So (safe due to data invariant) ...
    return pointee_address_equal(this->current, op.current);
  }


  /// [4]. Widen hint
 
  // Use default : without history there is no reason to say any location
  // is better than another to widen.
}


/// TODO class calling_context_historyt : public ai_history_baset { ... }

#undef IMPLIES
 
#endif // CPROVER_ANALYSES_AI_HISTORY_H
