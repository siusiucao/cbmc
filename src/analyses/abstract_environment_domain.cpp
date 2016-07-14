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

#include "map_domain.h"

/*******************************************************************\

Function: abstract_enivornmentt::trackable

  Inputs: An expression e

 Outputs: A boolean indicating whether the expression is trackable or not.

 Purpose: Identifying expressions who's values can be read / written.

\*******************************************************************/

template<class domainT>
bool abstract_enivornmentt::trackable (const exprt &e) const {
  return e.id()==ID_symbol ||
    e.id()==ID_index ||
    e.id()==ID_member ||
    e.id()==ID_dereference;
}

/*******************************************************************\

Function: abstract_enivornmentt::is_tracked

  Inputs: An expression e that is trackable.

 Outputs: A boolean indicating whether the expression is tracked (and
          thus can be read or written)

 Purpose: Working out whether a given expression has a value in the
          abstract environment.

\*******************************************************************/

template<class domainT>
bool abstract_environmentt::is_tracked (const exprt &e) const {
  assert(trackable(e));
  
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
}

/*******************************************************************\

Function: abstract_enivornmentt::track

  Inputs: An expression e that is trackable.

 Outputs: Nothing.

 Purpose: Starts tracking the expression and initialises its value to top.

\*******************************************************************/

template<class domainT>
void abstract_environmentt::track (const exprt &e) {
  assert(trackable(e));

  domainT init;
  init.make_top();
  
  expression_sett mapped(lookup(e));

  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    if (dom.find(*i) == dom.end())
    {
      dom.insert(*i, init);
    }
  }

  return;
}



/*******************************************************************\

Function: abstract_enivornmentt::read

  Inputs: An expression e that is currently tracked.

 Outputs: An abstract element representing the current value in the
          abstract domain.

 Purpose: One of the fundamental options of an environment, allows the
          value of a tracked expression to be accessed.

\*******************************************************************/

template<class domainT>
domainT abstract_environmentt::read (const exprt &e) const {
  assert(is_tracked(e));

  domainT output;
  output.make_top();
  
  expression_sett mapped(lookup(e));

  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    assert(dom.find(*i) != dom.end());
    output.join(dom[*i]);
  }

  return output;
}


/*******************************************************************\

Function: abstract_enivornmentt::write

  Inputs: An expression e that is currently tracked and an abstract
          value to assign.

 Outputs: Nothing.

 Purpose: One of the fundamental operations of an environment, allows
          the value of a tracked expression to be updated.

\*******************************************************************/

template<class domainT>
void abstract_environmentt::write (const exprt &e, const domainT &d) {
  assert(is_tracked(e));

  expression_sett mapped(lookup(e));

  for (expression_sett::const_iterator i = mapped.begin();
       i != mapped.end();
       ++i)
  {
    assert(dom.find(*i) != dom.end());
    dom[*i] = d;
  }

  return;
}


/*******************************************************************\

Function: abstract_enivornmentt::lookup

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
expression_sett abstract_environmentt::lookup (const exprt &e) {
  assert(trackable(e));

  switch (e.id())
  {
  case ID_symbol :
  case ID_index :
  case ID_member :
  case ID_dereference :
  default :
  }

  return;
}



/*******************************************************************\

Function: abstract_enivornmentt::

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/

/*******************************************************************\

Function: abstract_enivornmentt::

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/

/*******************************************************************\

Function: abstract_enivornmentt::

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/




/*******************************************************************\

Function: abstract_enivornment_domaint::transform

  Inputs: The instruction before (from) and after (to) the abstract domain,
          the abstract interpreter (ai) and the namespace (ns).

 Outputs: None

 Purpose: Compute the abstract transformer for a single instruction

\*******************************************************************/
void abstract_enivornment_domaint::transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) {
  std::cerr << "abstract_enivornment_domaint::transform()\n";

  #if 0
  const goto_programt::instructiont &instruction=*from;
  switch(instruction.type)
  {
  case GOTO:
    // TODO : Only use for information flow
    break;

  case ASSUME:
  case ASSERT:
    // Conditions on the program, do not alter the data or information
    // flow and thus can be ignored.
    break;

  case OTHER:
    // Defensive
    assert(0);
    break;

  case START_THREAD:
    break;

  case END_THREAD:
    break;

  case LOCATION:
    break;

  case END_FUNCTION:
    break;

  case ATOMIC_BEGIN:
    break;

  case ATOMIC_END:
    break;

  case RETURN:
    break;
  
  case ASSIGN:
    break;

  case DECL:
    break;
    
  case DEAD:
    break;
    
  case FUNCTION_CALL:
    break;

  case THROW:
    break;

  case CATCH:
    break;
    
  default:;
  }
  #endif
  
  return;
}

/*******************************************************************\

Function: abstract_enivornment_domaint::output

  Inputs: The output stream (out), the abstract interpreter (ai) and
          the namespace.

 Outputs: None

 Purpose: Basic text output of the abstract domain

\*******************************************************************/
void abstract_enivornment_domaint::output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const {
  std::cerr << "abstract_enivornment_domaint::output()\n";

  out << "{\n";

  for (mapt::const_iterator i = dom.begin();
       i != dom.end();
       ++i) {
    out << i->first << " -> ";
    i->second.output(out, ai, ns);
    }
  }
  
  out << "}\n";
}
  
/*******************************************************************\

Function: abstract_enivornment_domaint::make_bottom

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to bottom (no relations).

\*******************************************************************/
void abstract_enivornment_domaint::make_bottom() {
  std::cerr << "abstract_enivornment_domaint::make_bottom()\n";

  dom.clear();
  return;
}

/*******************************************************************\

Function: abstract_enivornment_domaint::make_top

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to top (all relations).

\*******************************************************************/
void abstract_enivornment_domaint::make_top() {
  std::cerr << "abstract_enivornment_domaint::make_entry()\n";
  assert(0);
}
  
/*******************************************************************\

Function: abstract_enivornment_domaint::make_entry

  Inputs: None

 Outputs: None

 Purpose: Set up a sane entry state.

\*******************************************************************/
void abstract_enivornment_domaint::make_entry() {
  std::cerr << "abstract_enivornment_domaint::make_entry()\n";
  assert(0);
}
  
/*******************************************************************\

Function: abstract_enivornment_domaint::merge

  Inputs: The other domain (b) and it's preceeding location (from) and
          current location (to).

 Outputs: True if something has changed

 Purpose: Computes the join between "this" and "b". 

\*******************************************************************/
bool abstract_enivornment_domaint::merge(const abstract_enivornment_domaint &b,
	     locationt from,
	     locationt to) {
  std::cerr << "abstract_enivornment_domaint::merge()\n";
  
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
