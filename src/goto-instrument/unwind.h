/*******************************************************************\

Module: Loop unwinding

Author: Daniel Kroening, kroening@kroening.com
        Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UNWIND_H
#define CPROVER_UNWIND_H

#include <goto-programs/goto_program.h>

// -1: do not unwind loop
typedef std::map<irep_idt, std::map<unsigned, int>> unwind_sett;

void parse_unwindset(const std::string &us, unwind_sett &unwind_set);

class goto_unwindt
{
public:
  typedef enum { REST, PARTIAL, ASSERT, ASSUME } unwind_strategyt;

  // unwind loop

  void unwind(
    goto_programt &goto_program,
    const goto_programt::const_targett loop_head,
    const goto_programt::const_targett loop_exit,
    const unsigned k, // bound for given loop
    const unwind_strategyt unwind_strategy) const;

  void unwind(
    goto_programt &goto_program,
    const goto_programt::const_targett loop_head,
    const goto_programt::const_targett loop_exit,
    const unsigned k, // bound for given loop
    const unwind_strategyt unwind_strategy,
    std::vector<goto_programt::targett> &iteration_points) const;

  // unwind function

  void unwind(
    goto_programt &goto_program,
    const unwind_sett &unwind_set,
    const int k=-1, // -1: no global bound
    const unwind_strategyt unwind_strategy=PARTIAL) const;

  // unwind all functions

  void operator()(
    goto_functionst &goto_functions,
    const unsigned k, // global bound
    const unwind_strategyt unwind_strategy=PARTIAL) const
  {
    const unwind_sett unwind_set;
    operator()(goto_functions, unwind_set, (int)k, unwind_strategy);
  }

  void operator()(
    goto_functionst &goto_functions,
    const unwind_sett &unwind_set,
    const int k=-1, // -1: no global bound
    const unwind_strategyt unwind_strategy=PARTIAL) const;

protected:
  int get_k(
    const irep_idt func,
    const unsigned loop_id,
    const int global_k,
    const unwind_sett &unwind_set) const;

  // copy goto program segment and redirect internal edges
  void copy_segment(
    const goto_programt::const_targett start,
    const goto_programt::const_targett end, // exclusive
    goto_programt &goto_program) const; // result

  goto_programt::targett get_mutable(
    goto_programt &goto_program,
    const goto_programt::const_targett t) const
  {
    return goto_program.instructions.erase(t, t);
  }
};

#endif
