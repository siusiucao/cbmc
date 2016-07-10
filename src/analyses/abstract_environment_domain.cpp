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

 Purpose: Identifying expressions who's values can be read / written

\*******************************************************************/

bool abstract_enivornmentt::trackable (const expr &e) {
  assert(0);
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
