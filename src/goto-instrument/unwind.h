/*******************************************************************\

Module: Loop unwinding

Author: Daniel Kroening, kroening@kroening.com
        Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UNWIND_H
#define CPROVER_UNWIND_H

#include <util/i2string.h>
#include <util/json.h>
#include <util/json_expr.h>
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
    const unwind_strategyt unwind_strategy);

  void unwind(
    goto_programt &goto_program,
    const goto_programt::const_targett loop_head,
    const goto_programt::const_targett loop_exit,
    const unsigned k, // bound for given loop
    const unwind_strategyt unwind_strategy,
    std::vector<goto_programt::targett> &iteration_points);

  // unwind function

  void unwind(
    goto_programt &goto_program,
    const unwind_sett &unwind_set,
    const int k=-1, // -1: no global bound
    const unwind_strategyt unwind_strategy=PARTIAL);

  // unwind all functions

  void operator()(
    goto_functionst &goto_functions,
    const unsigned k, // global bound
    const unwind_strategyt unwind_strategy=PARTIAL)
  {
    const unwind_sett unwind_set;
    operator()(goto_functions, unwind_set, (int)k, unwind_strategy);
  }

  void operator()(
    goto_functionst &goto_functions,
    const unwind_sett &unwind_set,
    const int k=-1, // -1: no global bound
    const unwind_strategyt unwind_strategy=PARTIAL);

  // unwind log

  void show_log_json(std::ostream &out) const
  {
    unwind_log.show_log_json(out);
  }

  // log for each copied instruction the location number of the
  // original instruction it came from; new instructions are
  // associated with the location of the backedge
  struct unwind_logt
  {
    // call after calling goto_functions.update()!
    void show_log_json(std::ostream &out) const;

    // remove entries that refer to the given goto program
    void cleanup(const goto_programt &goto_program)
    {
      forall_goto_program_instructions(it, goto_program)
        location_map.erase(it);
    }

    void insert(
      const goto_programt::const_targett target,
      const unsigned location_number)
    {
      assert(location_map.find(target)==location_map.end());
      location_map[target]=location_number;
    }

    typedef std::map<goto_programt::const_targett, unsigned> location_mapt;
    location_mapt location_map;
  };

protected:
  unwind_logt unwind_log;

  int get_k(
    const irep_idt func,
    const unsigned loop_id,
    const int global_k,
    const unwind_sett &unwind_set) const;

  // copy goto program segment and redirect internal edges
  void copy_segment(
    const goto_programt::const_targett start,
    const goto_programt::const_targett end, // exclusive
    goto_programt &goto_program); // result

  goto_programt::targett get_mutable(
    goto_programt &goto_program,
    const goto_programt::const_targett t) const
  {
    return goto_program.instructions.erase(t, t);
  }
};

#endif
