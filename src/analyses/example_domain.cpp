/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

\*******************************************************************/

#include <iostream>

#include "example_domain.h"

example_domaint::example_domaint()
{
  // This must set the domain to bottom i.e. "no possible values"
  make_bottom();
}

example_domaint::~example_domaint()
{
  // You probably don't need anything here
}

// Transform updates the domain with the effect of the instruction "from"
void example_domaint::transform(
  const irep_idt &function_from,
  locationt from,
  const irep_idt &function_to,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  std::cerr << "Example domain @ 0x" << this << " transform using instruction "
            << from->location_number << '\n';

  // If e is an exprt (an expression) then
  //   std::cerr << e.pretty()
  // prints it out

  const goto_programt::instructiont &instruction = *from;
  switch(instruction.type)
  {
    /** These are the instructions you actually need to implement **/
  case DECL:
    // Creates a new variable to_code_decl(instruction.code).symbol()
    break;

  case DEAD:
    // Says that to_code_dead(instruction.code).symbol() is no longer needed
    break;

  case ASSIGN:
    // Set to_code_assign(instruction.code).lhs() to
    //     to_code_assign(instruction.code).rhs()
    break;

  case GOTO:
  {
    // Comparing iterators is safe as the target must be within the same list
    // of instructions because this is a GOTO.
    locationt next = from;
    next++;
    if(from->get_target() != next) // If equal then a skip
    {
      if(next == to)
      {
        // Branch is not taken
      }
      else
      {
        // Branch is taken
      }
    }
    break;
  }

  case FUNCTION_CALL:
  {
    // Function calls are a bit of a fiddle...
    // const code_function_callt &code_function_call =
    //   to_code_function_call(instruction.code);
    break;
  }

  case ASSUME:
    // It is safe to over-approximate these by ... ignoring them!
    break;

    /** These are instructions you really can ignore **/
  case CATCH:
  case THROW:
    DATA_INVARIANT(false, "Exceptions must be removed before analysis");
    break;
  case RETURN:
    DATA_INVARIANT(false, "Returns must be removed before analysis");
    break;
  case ATOMIC_BEGIN: // Ignoring is a valid over-approximation
  case ATOMIC_END:   // Ignoring is a valid over-approximation
  case END_FUNCTION: // No action required
  case START_THREAD: // Require a concurrent analysis at higher level
  case END_THREAD:   // Require a concurrent analysis at higher level
  case ASSERT:       // No action required
  case LOCATION:     // No action required
  case SKIP:         // No action required
    break;
  case OTHER:
#if 0
    DATA_INVARIANT(false, "Unclear what is a safe over-approximation of OTHER");
#endif
    break;
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    DATA_INVARIANT(false, "Only complete instructions can be analyzed");
    break;
  }

  return;
}

// Merges two domains together
bool example_domaint::merge(const example_domaint &b, locationt, locationt)
{
  std::cerr << "Example domain @ 0x" << this << " merge in example domain @ 0x"
            << &b << '\n';

  return true;
}

void example_domaint::make_bottom()
{
}

void example_domaint::make_top()
{
}

void example_domaint::make_entry()
{
  // This is fine for almost everyone
  make_top();
}

bool example_domaint::is_bottom() const
{
  return true;
}

bool example_domaint::is_top() const
{
  return false; // Seriously change this!
}

void example_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  out << "Example domain @ 0x" << this;
  return;
}
