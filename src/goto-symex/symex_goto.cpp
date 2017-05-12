/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <algorithm>

#include <util/std_expr.h>

#include <analyses/dirty.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_goto(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  statet::framet &frame=state.top();

  exprt old_guard=instruction.guard;
  clean_expr(old_guard, state, false);

  exprt new_guard=old_guard;
  state.rename(new_guard, ns);
  do_simplify(new_guard);

  if(new_guard.is_false() ||
     state.guard.is_false())
  {
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);

    // reset unwinding counter
    if(instruction.is_backwards_goto())
      frame.loop_iterations[goto_programt::loop_id(state.source.pc)].count=0;

    // next instruction
    state.source.pc++;
    return; // nothing to do
  }

  target.goto_instruction(state.guard.as_expr(), new_guard, state.source);

  ASSERT(!instruction.targets.empty());

  // we only do deterministic gotos for now
  if(instruction.targets.size()!=1)
    throw "no support for non-deterministic gotos";

  goto_programt::const_targett goto_target=
    instruction.get_target();

  bool forward=!instruction.is_backwards_goto();

  if(!forward) // backwards?
  {
    unsigned &unwind=
      frame.loop_iterations[goto_programt::loop_id(state.source.pc)].count;
    unwind++;

    // continue unwinding?
    if(get_unwind(state.source, unwind))
    {
      // no!
      loop_bound_exceeded(state, new_guard);

      // reset unwinding
      unwind=0;

      // next instruction
      state.source.pc++;
      return;
    }

    if(new_guard.is_true())
    {
      state.source.pc=goto_target;
      return; // nothing else to do
    }
  }

  goto_programt::const_targett new_state_pc, state_pc;
  symex_targett::sourcet original_source=state.source;

  if(forward)
  {
    new_state_pc=goto_target;
    state_pc=state.source.pc;
    state_pc++;

    // skip dead instructions
    if(new_guard.is_true())
      while(state_pc!=goto_target && !state_pc->is_target())
        ++state_pc;

    if(state_pc==goto_target)
    {
      state.source.pc=goto_target;
      return; // nothing else to do
    }
  }
  else
  {
    new_state_pc=state.source.pc;
    new_state_pc++;
    state_pc=goto_target;
  }

  state.source.pc=state_pc;

  // put into state-queue
  statet::goto_state_listt &goto_state_list=
    state.top().goto_state_map[new_state_pc];

  goto_state_list.push_back(statet::goto_statet(state));
  statet::goto_statet &new_state=goto_state_list.back();

  // adjust guards
  if(new_guard.is_true())
  {
    state.guard.make_false();
  }
  else
  {
    // produce new guard symbol
    exprt guard_expr;

    if(new_guard.id()==ID_symbol ||
       (new_guard.id()==ID_not &&
        new_guard.operands().size()==1 &&
        new_guard.op0().id()==ID_symbol))
      guard_expr=new_guard;
    else
    {
      symbol_exprt guard_symbol_expr=
        symbol_exprt(guard_identifier, bool_typet());
      exprt new_rhs=new_guard;
      new_rhs.make_not();

      ssa_exprt new_lhs(guard_symbol_expr);
      state.rename(new_lhs, ns, goto_symex_statet::L1);
      state.assignment(new_lhs, new_rhs, ns, true, false);

      guardt guard;

      target.assignment(
        guard.as_expr(),
        new_lhs, new_lhs, guard_symbol_expr,
        new_rhs,
        original_source,
        symex_targett::GUARD);

      guard_expr=guard_symbol_expr;
      guard_expr.make_not();
      state.rename(guard_expr, ns);
    }

    if(forward)
    {
      new_state.guard.add(guard_expr);
      guard_expr.make_not();
      state.guard.add(guard_expr);
    }
    else
    {
      state.guard.add(guard_expr);
      guard_expr.make_not();
      new_state.guard.add(guard_expr);
    }
  }
}

/*******************************************************************\

Function: goto_symext::symex_step_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_step_goto(statet &state, bool taken)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  exprt guard(instruction.guard);
  dereference(guard, state, false);
  state.rename(guard, ns);

  if(!taken)
    guard.make_not();

  state.guard.guard_expr(guard);
  do_simplify(guard);

  target.assumption(state.guard.as_expr(), guard, state.source);
}

/*******************************************************************\

Function: goto_symext::merge_gotos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::merge_gotos(statet &state)
{
  statet::framet &frame=state.top();

  // first, see if this is a target at all
  statet::goto_state_mapt::iterator state_map_it=
    frame.goto_state_map.find(state.source.pc);

  if(state_map_it==frame.goto_state_map.end())
    return; // nothing to do

  // we need to merge
  statet::goto_state_listt &state_list=state_map_it->second;

  for(statet::goto_state_listt::reverse_iterator
      list_it=state_list.rbegin();
      list_it!=state_list.rend();
      list_it++)
  {
    statet::goto_statet &goto_state=*list_it;

    // check atomic section
    if(state.atomic_section_id!=goto_state.atomic_section_id)
      throw "atomic sections differ across branches";

    // do SSA phi functions
    phi_function(goto_state, state);

    merge_value_sets(goto_state, state);

    // adjust guard
    state.guard|=goto_state.guard;

    // adjust depth
    state.depth=std::min(state.depth, goto_state.depth);
  }

  // clean up to save some memory
  frame.goto_state_map.erase(state_map_it);
}

/*******************************************************************\

Function: goto_symext::merge_value_sets

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::merge_value_sets(
  const statet::goto_statet &src,
  statet &dest)
{
  if(dest.guard.is_false())
  {
    dest.value_set=src.value_set;
    return;
  }

  dest.value_set.make_union(src.value_set);
}

/*******************************************************************\

Function: goto_symext::phi_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::phi_function(
  const statet::goto_statet &goto_state,
  statet &dest_state)
{
  // go over all variables to see what changed
  std::unordered_set<ssa_exprt, irep_hash> variables;

  goto_state.level2_get_variables(variables);
  dest_state.level2.get_variables(variables);

  for(std::unordered_set<ssa_exprt, irep_hash>::const_iterator
      it=variables.begin();
      it!=variables.end();
      it++)
  {
    const irep_idt l1_identifier=it->get_identifier();
    const irep_idt &obj_identifier=it->get_object_name();

    if(obj_identifier==guard_identifier)
      continue; // just a guard, don't bother

    if(goto_state.level2_current_count(l1_identifier)==
       dest_state.level2.current_count(l1_identifier))
      continue; // not at all changed

    // changed!

    // shared variables are renamed on every access anyway, we don't need to
    // merge anything
    const symbolt &symbol=ns.lookup(obj_identifier);

    // shared?
    if(dest_state.atomic_section_id==0 &&
       dest_state.threads.size()>=2 &&
       (symbol.is_shared() || (*dest_state.dirty)(symbol.name)))
      continue; // no phi nodes for shared stuff

    // don't merge (thread-)locals across different threads, which
    // may have been introduced by symex_start_thread (and will
    // only later be removed from level2.current_names by pop_frame
    // once the thread is executed)
    if(!it->get_level_0().empty() &&
       it->get_level_0()!=std::to_string(dest_state.source.thread_nr))
      continue;

    exprt goto_state_rhs=*it, dest_state_rhs=*it;

    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        goto_state.propagation.values.find(l1_identifier);

      if(p_it!=goto_state.propagation.values.end())
        goto_state_rhs=p_it->second;
      else
        to_ssa_expr(goto_state_rhs).set_level_2(
          goto_state.level2_current_count(l1_identifier));
    }

    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        dest_state.propagation.values.find(l1_identifier);

      if(p_it!=dest_state.propagation.values.end())
        dest_state_rhs=p_it->second;
      else
        to_ssa_expr(dest_state_rhs).set_level_2(
          dest_state.level2.current_count(l1_identifier));
    }

    exprt rhs;

    if(dest_state.guard.is_false())
      rhs=goto_state_rhs;
    else if(goto_state.guard.is_false())
      rhs=dest_state_rhs;
    else
    {
      guardt tmp_guard(goto_state.guard);

      // this gets the diff between the guards
      tmp_guard-=dest_state.guard;

      rhs=if_exprt(tmp_guard.as_expr(), goto_state_rhs, dest_state_rhs);
      do_simplify(rhs);
    }

    ssa_exprt new_lhs=*it;
    const bool record_events=dest_state.record_events;
    dest_state.record_events=false;
    dest_state.assignment(new_lhs, rhs, ns, true, true);
    dest_state.record_events=record_events;

    target.assignment(
      true_exprt(),
      new_lhs, new_lhs, new_lhs.get_original_expr(),
      rhs,
      dest_state.source,
      symex_targett::PHI);
  }
}

/*******************************************************************\

Function: goto_symext::loop_bound_exceeded

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::loop_bound_exceeded(
  statet &state,
  const exprt &guard)
{
  const unsigned loop_number=state.source.pc->loop_number;

  exprt negated_cond;

  if(guard.is_true())
    negated_cond=false_exprt();
  else
    negated_cond=not_exprt(guard);

  bool unwinding_assertions=
    options.get_bool_option("unwinding-assertions");

  bool partial_loops=
    options.get_bool_option("partial-loops");

  if(!partial_loops)
  {
    if(unwinding_assertions)
    {
      // Generate VCC for unwinding assertion.
      vcc(negated_cond,
          "unwinding assertion loop "+std::to_string(loop_number),
          state);

      // add to state guard to prevent further assignments
      state.guard.add(negated_cond);
    }
    else
    {
      // generate unwinding assumption, unless we permit partial loops
      symex_assume(state, negated_cond);
    }
  }
}

/*******************************************************************\

Function: goto_symext::get_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_symext::get_unwind(
  const symex_targett::sourcet &source,
  unsigned unwind)
{
  // by default, we keep going
  return false;
}
