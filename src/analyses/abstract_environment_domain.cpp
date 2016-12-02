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
#define UNREACHABLE(r) throw "Unreachable: " r
#define UNSUPPORTED(r) throw "Unsupported: " r
#define INTERNAL_INVARIANT(r) throw "Internal invariant: " r
#define UNIMPLEMENTED(r) throw "Unimplemented: " r
#endif

#define DEFENSIVE

#ifdef DEFENSIVE
#define DEFENSIVE_UNHANDLED(X) UNIMPLEMENTED(X)
#else
#define DEFENSIVE_UNHANDLED(X) do { } while(0)
#endif

//#define LOGGING
#ifdef LOGGING
#define LOG(X) X
#else
#define LOG(X) do { } while(0)
#endif






/*******************************************************************\

Function: abstract_environment_domaint::transform

  Inputs: The instruction before (from) and after (to) the abstract domain,
          the abstract interpreter (ai) and the namespace (ns).

 Outputs: None

 Purpose: Compute the abstract transformer for a single instruction

\*******************************************************************/

void abstract_environment_domaint::transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) {
  LOG(std::cerr << "abstract_environment_domaint::transform()\n");
  domainT d;
  
  const goto_programt::instructiont &instruction=*from;
  switch(instruction.type)
  {
  case DECL:
    // Creates a new variable, which should be top
    // but we don't store top so ... no action required
    break;
    
  case DEAD:
    // Assign to top is the same as removing
    d.make_top();
    assign(to_code_dead(instruction.code).symbol(), d);
    break;

  case ASSIGN:
    {
      const code_assignt &inst = to_code_assign(instruction.code);

      // TODO : check return values
      abstract_objectt *r = eval(inst.rhs());
      assign(inst.lhs(), *r);
    }
    break;

  case GOTO:
    {
      if (flow_sensitivity == FLOW_SENSITIVE)
      {
	locationt next=from;
	next++;
	if(next==to)
	  assume(not_exprt(instruction.guard));
	else
	  assume(instruction.guard);
      }
    }
    break;

  case ASSUME:
    assume(instruction.guard);
    break;
    
  case FUNCTION_CALL:
    // FIXME : Ignore as not yet interprocedural
    break;

  case END_FUNCTION:
    // FIXME : Ignore as not yet interprocedural
    break;

    /***************************************************************/

  case ASSERT:
    // Conditions on the program, do not alter the data or information
    // flow and thus can be ignored.
    break;

  case SKIP:
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
  
  return;
}

/*******************************************************************\

Function: abstract_environment_domaint::output

  Inputs: The output stream (out), the abstract interpreter (ai) and
          the namespace.

 Outputs: None

 Purpose: Basic text output of the abstract domain

\*******************************************************************/
void abstract_environment_domaint::output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const {
  LOG(std::cerr << "abstract_environment_domaint::output()\n");

  out << "{\n";

  for (typename mapt::const_iterator i = dom.begin();
       i != dom.end();
       ++i) {
    out << i->first << " (" << i->second.concrete_location << ") -> ";
    i->second.element.output(out, ai, ns);
  }

  out << "}\n";
}
  
/*******************************************************************\

Function: abstract_environment_domaint::make_bottom

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to bottom (no relations).

\*******************************************************************/
void abstract_environment_domaint::make_bottom() {
  LOG(std::cerr << "abstract_environment_domaint::make_bottom()\n");

  is_bottom = true;
  dom.clear();       // Not strictly needed but keeps things simple

  return;
}

/*******************************************************************\

Function: abstract_environment_domaint::make_top

  Inputs: None

 Outputs: None

 Purpose: Sets the domain to top (all relations).

\*******************************************************************/
void abstract_environment_domaint::make_top() {
  LOG(std::cerr << "abstract_environment_domaint::make_top()\n");

  is_bottom = false;
  dom.clear();       // Do not store things that are top

  return;
}

  
/*******************************************************************\

Function: abstract_environment_domaint::make_entry

  Inputs: None

 Outputs: None

 Purpose: Set up a sane entry state.

\*******************************************************************/
void abstract_environment_domaint::make_entry() {
  LOG(std::cerr << "abstract_environment_domaint::make_entry()\n");
  assert(0);
}
  
/*******************************************************************\

Function: abstract_environment_domaint::merge

  Inputs: The other domain (b) and it's preceeding location (from) and
          current location (to).

 Outputs: True if something has changed.

 Purpose: Computes the join between "this" and "b". 

\*******************************************************************/
bool abstract_environment_domaint::merge(const abstract_environment_domaint &b,
	     locationt from,
	     locationt to) {
  LOG(std::cerr << "abstract_environment_domaint::merge()\n");

  // Use the abstract_environment merge

  UNREACHABLE("merge case not handled");
  return true;
}





