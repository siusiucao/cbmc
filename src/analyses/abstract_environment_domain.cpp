/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: April 2016

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
*/
#include <util/message.h>

#include "abstract_environment_domain.h"

#ifdef DEBUG
#define UNREACHABLE(r) std::cerr << r << std::endl; assert(0)
#define UNSUPPORTED(r) std::cerr << r << std::endl; assert(0)
#define INTERNAL_INVARIANT(r) std::cerr << r << std::endl; assert(0)
#define UNIMPLEMENTED(r) std::cerr << r << std::endl; assert(0)
#else
#define UNREACHABLE(r) throw "Unreachable"
#define UNSUPPORTED(r) throw "Unsupported"
#define INTERNAL_INVARIANT(r) throw "Internal invariant"
#define UNIMPLEMENTED(r) throw "Unimplemented"
#endif

/*******************************************************************\

Function: abstract_environmentt::trackable

  Inputs: An expression e

 Outputs: A boolean indicating whether the expression is trackable or not.

 Purpose: Identifying expressions who's values can be read / written.
          Should fit with what can be assigned in a goto-program.

\*******************************************************************/

template<class domainT>
bool abstract_environmentt<domainT>::trackable (const exprt &e) const {
  return e.id()==ID_symbol ||
    e.id()==ID_index ||
    e.id()==ID_member ||
    e.id()==ID_dereference;
}

/*******************************************************************\

Function: abstract_environmentt::is_tracked

  Inputs: An expression e that is trackable.

 Outputs: A boolean indicating whether the expression is tracked (and
          thus can be read or written)

 Purpose: Working out whether a given expression has a value in the
          abstract environment.
          This is the 'default' behaviour and thus just adds
          everything as concrete.

\*******************************************************************/

template<class domainT>
bool abstract_environmentt<domainT>::is_tracked (const exprt &e) const {
  assert(trackable(e));

  #if 0
  expression_sett mapped(lookup(e));

  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    if (dom.find(*i) == dom.end())
    {
      return false;
    }
  }

  return true;
  #endif

  return dom.find(e) != dom.end();
}

/*******************************************************************\

Function: abstract_environmentt::track

  Inputs: An expression e that is trackable and a Boolean noting
          whether it is a concrete location or not.

 Outputs: Nothing.

 Purpose: Starts tracking the expression and initialises its value to
          top.  Abstract locations are ones that represent multiple
          memory addresses, thus writes to them are joins rather than
          normal writes.
          This is the 'default' behaviour and thus just adds
          everything as concrete.

\*******************************************************************/

template<class domainT>
void abstract_environmentt<domainT>::track (const exprt &e, bool concrete_location) {
  assert(trackable(e));

  domainT init;
  init.make_top();
#if 0  
  expression_sett mapped(lookup(e));

  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    if (dom.find(*i) == dom.end())
    {
      dom.insert(*i, abstract_cellt(init, concrete_location));
    }
    
  }
#endif
  if (dom.find(e) == dom.end())
  {
    dom.insert(e, abstract_cellt(init, concrete_location));
  } else {
    INTERNAL_INVARIANT(std::string("Expression already tracked ") + e.pretty());
  }
  
  return;
}

/*******************************************************************\

Function: abstract_environmentt::untrack

  Inputs: An expression e that is trackable.

 Outputs: Nothing.

 Purpose: Stops tracking the expression.  References that translate to
          this element will now fail.
          This is the 'default' behaviour and thus just adds
          everything as concrete.

\*******************************************************************/

template<class domainT>
void abstract_environmentt<domainT>::untrack (const exprt &e) {
  assert(trackable(e));

#if 0
  expression_sett mapped(lookup(e));

  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    dom.erase(*i);
  }
#endif
  if (dom.find(e) == dom.end())
  {
    INTERNAL_INVARIANT(std::string("Expression not tracked ") + e.pretty());
  } else {
    dom.erase(e);
  }

  return;
}



/*******************************************************************\

Function: abstract_environmentt::read

  Inputs: An expression e that is currently tracked.

 Outputs: An abstract element representing the current value in the
          abstract domain.

 Purpose: One of the fundamental options of an environment, allows the
          value of a tracked expression to be accessed.

\*******************************************************************/

template<class domainT>
domainT abstract_environmentt<domainT>::read (const exprt &e) const {
  assert(is_tracked(e));

  domainT output;
  output.make_top();
  
  expression_sett mapped(lookup(e));

  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    assert(dom.find(*i) != dom.end());
    output.join(dom[*i].element);
  }

  return output;
}


/*******************************************************************\

Function: abstract_environmentt::write

  Inputs: An expression e that is currently tracked and an abstract
          value to assign.

 Outputs: Nothing.

 Purpose: One of the fundamental operations of an environment, allows
          the value of a tracked expression to be updated.

\*******************************************************************/

template<class domainT>
void abstract_environmentt<domainT>::write (const exprt &e, const domainT &d) {
  assert(is_tracked(e));

  expression_sett mapped(lookup(e));
  bool single_location_write = (mapped.size() == 1);
  
  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    assert(dom.find(*i) != dom.end());

    if (single_location_write && dom[*i]->concrete_location)
      dom[*i] = d;
    else
      dom[*i].join(d);
  }

  return;
}


/*******************************************************************\

Function: abstract_environmentt::lookup

  Inputs: A trackable expression e

 Outputs: A set of expressions giving the entries in the domain map that
          correspond to the input expression.

 Purpose: This is the entry point to the second part of the
          abstraction in the abstract environment, mapping from the
          expression that is read / written to the expressions that
          are tracked.  By overloading various of the lookup_* methods
          it is possible to combine or split values.  For example, all
          writes to an array can be coallesced to a single stored
          abstract value or writes to non-constant locations can be
          expanded to cover all possible values.

\*******************************************************************/

template<class domainT>
expression_sett abstract_environmentt<domainT>::lookup (const exprt &e) const {
  assert(trackable(e));

  switch (e.id())
  {
  case ID_symbol :
    switch (e.type().id()) {
    case ID_struct :
      return lookup_structure(e);
      break;
      
    case ID_union :
      return lookup_union(e);
      break;
      
    case ID_array :
      return lookup_array(e);
      break;

    default :
      return lookup_symbol(e);
      break;
    }
    UNREACHABLE("case fall-throught");
    break;
    
  case ID_index :
    return lookup_array();
    break;
    
  case ID_member :
    if (e.type().id() == ID_struct) {
      return lookup_structure(e);
    } else if (e.type().id() == ID_union) {
      return lookup_union(e);
    } else {
      UNSUPPORTED(std::string("ID_member on unsupported type ") + e.type().pretty());
    }
    break;
    
  case ID_dereference :
    return lookup_dereference(e);
    break;
    
  default :
    return lookup_rest(e);
    break;
  }

  UNREACHABLE("case fall-through");
}



/*******************************************************************\

Function: abstract_environmentt::lookup_symbol

  Inputs: A trackable expression e

 Outputs: A set of expressions giving the entries in the domain map that
          correspond to the input expression.

 Purpose: The default behaviour is to map one-to-one.

\*******************************************************************/

template<class domainT>
expression_sett abstract_environmentt<domainT>::lookup_symbol (const exprt &e) const {
  assert(trackable(e));

  expression_sett s;
  s.insert(e);
  
  return s;
}

/*******************************************************************\

Function: abstract_environmentt::lookup_array

  Inputs: A trackable expression e

 Outputs: A set of expressions giving the entries in the domain map that
          correspond to the input expression.

 Purpose: The default behaviour is to map one-to-one.

\*******************************************************************/

template<class domainT>
expression_sett abstract_environmentt<domainT>::lookup_array (const exprt &e) const {
  assert(trackable(e));

  expression_sett s;
  s.insert(e);
  
  return s;
}

/*******************************************************************\

Function: abstract_environmentt::lookup_structure

  Inputs: A trackable expression e

 Outputs: A set of expressions giving the entries in the domain map that
          correspond to the input expression.

 Purpose: The default behaviour is to map one-to-one.

\*******************************************************************/

template<class domainT>
expression_sett abstract_environmentt<domainT>::lookup_structure (const exprt &e) const {
  assert(trackable(e));

  expression_sett s;
  s.insert(e);
  
  return s;
}

/*******************************************************************\

Function: abstract_environmentt::lookup_union

  Inputs: A trackable expression e

 Outputs: A set of expressions giving the entries in the domain map that
          correspond to the input expression.

 Purpose: The default behaviour is to map one-to-one.

\*******************************************************************/

template<class domainT>
expression_sett abstract_environmentt<domainT>::lookup_union (const exprt &e) const {
  assert(trackable(e));

  expression_sett s;
  s.insert(e);
  
  return s;
}

/*******************************************************************\

Function: abstract_environmentt::lookup_dereference

  Inputs: A trackable expression e

 Outputs: A set of expressions giving the entries in the domain map that
          correspond to the input expression.

 Purpose: The default behaviour is to map one-to-one.

\*******************************************************************/

template<class domainT>
expression_sett abstract_environmentt<domainT>::lookup_dereference (const exprt &e) const {
  assert(trackable(e));

  expression_sett s;
  s.insert(e);
  
  return s;
}
/*******************************************************************\

Function: abstract_environmentt::lookup_rest

  Inputs: A trackable expression e

 Outputs: A set of expressions giving the entries in the domain map that
          correspond to the input expression.

 Purpose: The default behaviour is to map one-to-one.

\*******************************************************************/

template<class domainT>
expression_sett abstract_environmentt<domainT>::lookup_rest (const exprt &e) const {
  assert(trackable(e));

  expression_sett s;
  s.insert(e);
  
  return s;
}










/*******************************************************************\

Function: abstract_environment_domaint::transform

  Inputs: The instruction before (from) and after (to) the abstract domain,
          the abstract interpreter (ai) and the namespace (ns).

 Outputs: None

 Purpose: Compute the abstract transformer for a single instruction

\*******************************************************************/
#define DEFENSIVE

#ifdef DEFENSIVE
#define DEFENSIVE_UNHANDLED(X) UNIMPLEMENTED(X)
#else
#define DEFENSIVE_UNHANDLED(X) do { } while(0)
#endif

template<class domainT>
void abstract_environment_domaint<domainT>::transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) {
  std::cerr << "abstract_environment_domaint::transform()\n";

  #if 0
  const goto_programt::instructiont &instruction=*from;
  switch(instruction.type)
  {
  case DECL:
    break;
    
  case DEAD:
    break;

  case ASSIGN:
    break;

  case GOTO:
    // TODO : Only use for information flow
    break;

  case ASSUME:
    break;
    
  case FUNCTION_CALL:
    break;

  case END_FUNCTION:
    UNIMPLEMENTED("End_function");
    break;

    /***************************************************************/

  case ASSERT:
    // Conditions on the program, do not alter the data or information
    // flow and thus can be ignored.
    break;
    
  case LOCATION:
    // Can ignore
    break;

  case RETURN:
    DEFENSIVE_UNHANDLED("Return instructions are depreciated");
    break;
    
  case START_THREAD:
  case END_THREAD:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
    DEFENSIVE_UNHANDLED("Threading not supported");
    break;    

  case THROW:
  case CATCH:
    DEFENSIVE_UNHANDLED("Exceptions not handled");
    break;

  case OTHER:
    DEFENSIVE_UNHANDLED("Other");
    break;
    
  default:
    DEFENSIVE_UNHANDLED("Unrecognised instruction type");
    break;
  }
  #endif
  
  return;
}

/*******************************************************************\

Function: abstract_environment_domaint::output

  Inputs: The output stream (out), the abstract interpreter (ai) and
          the namespace.

 Outputs: None

 Purpose: Basic text output of the abstract domain

\*******************************************************************/
template<class domainT>
void abstract_environment_domaint<domainT>::output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) {// const {
  std::cerr << "abstract_environment_domaint::output()\n";

  out << "{\n";

  out << x;
#if 0  
  for (typename mapt::const_iterator i = dom.begin();
       i != dom.end();
       ++i) {
    out << i->first << " -> ";
    i->second.output(out, ai, ns);
    }
  }
  #endif
  out << "}\n";
}
  
/*******************************************************************\

Function: abstract_environment_domaint::make_bottom

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to bottom (no relations).

\*******************************************************************/
template<class domainT>
void abstract_environment_domaint<domainT>::make_bottom() {
  std::cerr << "abstract_environment_domaint::make_bottom()\n";

  dom.clear();
  return;
}

/*******************************************************************\

Function: abstract_environment_domaint::make_top

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to top (all relations).

\*******************************************************************/
template<class domainT>
void abstract_environment_domaint<domainT>::make_top() {
  std::cerr << "abstract_environment_domaint::make_entry()\n";
  assert(0);
}
  
/*******************************************************************\

Function: abstract_environment_domaint::make_entry

  Inputs: None

 Outputs: None

 Purpose: Set up a sane entry state.

\*******************************************************************/
template<class domainT>
void abstract_environment_domaint<domainT>::make_entry() {
  std::cerr << "abstract_environment_domaint::make_entry()\n";
  assert(0);
}
  
/*******************************************************************\

Function: abstract_environment_domaint::merge

  Inputs: The other domain (b) and it's preceeding location (from) and
          current location (to).

 Outputs: True if something has changed

 Purpose: Computes the join between "this" and "b". 

\*******************************************************************/
template<class domainT>
bool abstract_environment_domaint<domainT>::merge(const abstract_environment_domaint &b,
	     locationt from,
	     locationt to) {
  std::cerr << "abstract_environment_domaint::merge()\n";
  
  bool hasChanged = false;

  // For each of the incoming dependencies
  for (dependency_mapt::const_iterator i = b.dom.begin();
       i != b.dom.end();
       ++i) {

    if (0) {
      // If it is new, add all of it
      hasChanged = true;
      
    } else {
      // Compute the union of the two dependency sets
      
    }
  }

  return hasChanged;
}


