/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS
#define CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS

#include <util/message.h>

#include "goto_functions.h"

class goto_inlinet:public messaget
{
public:
  goto_inlinet(
    goto_functionst &goto_functions,
    const namespacet &ns,
    message_handlert &message_handler):
    messaget(message_handler),
    goto_functions(goto_functions),
    ns(ns)
  {
  }

  typedef goto_functionst::goto_functiont goto_functiont;

  // call that should be inlined
  // false:    inline non-transitively
  // true:     inline transitively
  typedef std::pair<goto_programt::targett, bool> callt;

  // list of calls that should be inlined
  typedef std::list<callt> call_listt;

  // list of calls per function that should be inlined
  typedef std::map<irep_idt, call_listt> inline_mapt;

  // handle given goto function
  // force_full:
  // - true:  put skip on recursion and issue warning
  // - false: leave call on recursion
  void goto_inline(
    const irep_idt identifier,
    goto_functiont &goto_function,
    const inline_mapt &inline_map,
    const bool force_full=false);

  // handle all functions
  void goto_inline(
    const inline_mapt &inline_map,
    const bool force_full=false);

  void output_inline_map(
    std::ostream &out,
    const inline_mapt &inline_map);

  // is bp call
  static bool is_bp_call(goto_programt::const_targett target);
  // is normal or bp call
  static bool is_call(goto_programt::const_targett target);
  // get call info of normal or bp call
  static void get_call(
    goto_programt::const_targett target,
    exprt &lhs,
    exprt &function,
    exprt::operandst &arguments,
    exprt &constrain);

protected:
  goto_functionst &goto_functions;
  const namespacet &ns;
  
  void goto_inline_nontransitive(
    const irep_idt identifier,
    goto_functiont &goto_function,
    const inline_mapt &inline_map,
    const bool force_full);

  const goto_functiont &goto_inline_transitive(
    const irep_idt identifier,
    const goto_functiont &goto_function,
    const bool force_full);

  bool check_inline_map(const inline_mapt &inline_map) const;
  bool check_inline_map(
    const irep_idt identifier,
    const inline_mapt &inline_map) const;

  bool is_ignored(const irep_idt id) const;

  void clear()
  {
    cache.clear();
    finished_set.clear();
    recursion_set.clear();
    no_body_set.clear();
  }

  void expand_function_call(
    goto_programt &dest,
    const inline_mapt &inline_map,
    const bool transitive,
    const bool force_full,
    goto_programt::targett target);

  void insert_function_body(
    const goto_functiont &f,
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    const exprt &constrain);

  void insert_function_nobody(
    goto_programt &dest,
    const exprt &lhs,
    goto_programt::targett target,
    const symbol_exprt &function,
    const exprt::operandst &arguments);

  void replace_return(
    goto_programt &body,
    const exprt &lhs,
    const exprt &constrain);
    
  void parameter_assignments(
    const source_locationt &source_location,
    const irep_idt &function_name,
    const code_typet &code_type,
    const exprt::operandst &arguments,
    goto_programt &dest);

  void parameter_destruction(
    const source_locationt &source_location,
    const irep_idt &function_name,
    const code_typet &code_type,
    goto_programt &dest);

  // goto functions that were already inlined transitively
  typedef std::map<irep_idt, goto_functiont> cachet;
  cachet cache;

  typedef hash_set_cont<irep_idt, irep_id_hash> finished_sett;
  finished_sett finished_set;

  typedef hash_set_cont<irep_idt, irep_id_hash> recursion_sett;
  recursion_sett recursion_set;
  
  typedef hash_set_cont<irep_idt, irep_id_hash> no_body_sett;
  no_body_sett no_body_set;
};

#endif
