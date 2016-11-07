/*******************************************************************\

Module: Compute unwind bounds

Author: Daniel Poetzl

\*******************************************************************/

#include "unwind_bounds.h"

//#define DEBUG
//#define DEBUG_VERBOSE

/*******************************************************************\

Function: unwind_boundst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void unwind_boundst::output(std::ostream &out) const
{
  out << "Unwind bounds: ";

  // unwind bounds we found
  bool first=true;

  for(unwind_bound_mapt::const_iterator it=unwind_bound_map.begin();
      it!=unwind_bound_map.end(); it++)
  {
    if(!first)
      out << ",";
    else
      first=false;

    locationt l=it->first;
    int bound=it->second;

    irep_idt function=l->function;
    const goto_functiont &goto_function
      =goto_functions.function_map.at(function);
    assert(goto_function.body_available());
    const goto_programt &goto_program=goto_function.body;

    irep_idt loop_id=goto_program.loop_id(l);

    out << loop_id << ":" << bound;
  }

  out << "\n\nNo unwind bound found: ";

  // remaining loops
  first=true;

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_backwards_goto())
      {
        unwind_bound_mapt::const_iterator u_it=unwind_bound_map.find(i_it);
        if(u_it==unwind_bound_map.end())
        {
          irep_idt loop_id=goto_program.loop_id(i_it);

          if(!first)
            out << ",";
          else
            first=false;

          out << loop_id;
        }
      }
    }
  }

  out << "\n";
}
#endif

void unwind_boundst::output(std::ostream &out) const
{
  out << "Unwind bounds:\n";

  for(loop_sett::const_iterator l_it=all_loops.begin();
      l_it!=all_loops.end(); l_it++)
  {
    const locationt loop=*l_it;
    const goto_programt &goto_program=get_goto_program(loop);

    irep_idt loop_id=goto_program.loop_id(loop);
    out << loop_id << ": ";

    max_boundst::const_iterator it=max_bounds.find(loop);
    if(it!=max_bounds.end())
    {
      out << it->second;
    }
    else
    {
      out << "-";
    }

    out << "\n";
  }
}

/*******************************************************************\

Function: unwind_boundst::output_unwindset()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::output_unwindset(std::ostream &out) const
{
  bool had_one=false;

  for(loop_sett::const_iterator l_it=all_loops.begin();
      l_it!=all_loops.end(); l_it++)
  {
    const locationt loop=*l_it;
    const goto_programt &goto_program=get_goto_program(loop);

    max_boundst::const_iterator it=max_bounds.find(loop);
    if(it!=max_bounds.end())
    {
      int bound=it->second;
      assert(bound>=-1);
      if(bound!=-1)
      {
        irep_idt loop_id=goto_program.loop_id(loop);

        if(had_one)
          out << ", ";

        had_one=true;

        out << loop_id << ": ";
        out << bound;
      }

    }
  }

  out << "\n";
}

/*******************************************************************\

Function: unwind_boundst::output_state_map()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::output_state_map(
  std::ostream &out,
  const state_mapt &state_map) const
{
  out << "State map size: " << state_map.size() << "\n";

  for(state_mapt::const_iterator it=state_map.begin();
      it!=state_map.end(); it++)
  {
    const locationt l=it->first;
    const constant_propagator_domaint &cpd=it->second;

    out << "Location number: " << l->location_number << "\n";
    out << "State:\n";
    cpd.output(out, dummy, ns);
  }
}

/*******************************************************************\

Function: unwind_boundst::output_inner_loop_map()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::output_inner_loop_map(std::ostream &out) const
{
  out << "Inner loop map:\n";
  for(inner_loop_mapt::const_iterator it=inner_loop_map.begin();
      it!=inner_loop_map.end(); it++)
  {
    const loop_listt &loop_list=it->second;
    const locationt loop=it->first;

    out << loop->location_number << "->\n";

    for(loop_listt::const_iterator i_it=loop_list.begin();
        i_it!=loop_list.end(); i_it++)
    {
      const locationt inner_loop=*i_it;
      out << "  " << inner_loop->location_number << "\n";
    }
  }
}

/*******************************************************************\

Function: unwind_boundst::output_outer_loops()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::output_outer_loops(std::ostream &out) const
{
  out << "Outer loops:\n";
  for(loop_sett::const_iterator it=outer_loops.begin();
      it!=outer_loops.end(); it++)
  {
    const locationt loop=*it;
    assert(loop->is_backwards_goto());

    out << "Location: " << loop->location_number << "\n";

    const goto_programt &goto_program=get_goto_program(loop);
    const irep_idt id=goto_program.loop_id(loop);

    out << "Loop id: " << id << "\n";
  }
}

/*******************************************************************\

Function: unwind_boundst::fixpoint_loop()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::fixpoint_loop(
  const locationt loop,
  const constant_propagator_domaint &entry_state,
  state_mapt &state_map)
{
  assert(state_map.empty());

#ifdef DEBUG_VERBOSE
  std::cout << "========\n";
  std::cout << "Fixpoint loop entry state:\n";
  entry_state.output(std::cout, dummy, ns);
#endif

  const locationt loop_head=get_loop_head(loop);

  constant_propagator_domaint cpd=entry_state; // copy

  location_sett working_set;
  assert(working_set.empty());

  locationt src;
  locationt tgt;

  if(cond_at_head(loop))
  {
    // state at loop head
    state_map[loop_head]=entry_state; // copy
    assert(state_map.size()==1);

    src=loop_head;

    locationt next=loop_head;
    next++;
    tgt=next;
  }
  else
  {
    src=loop;
    tgt=loop_head;
  }

  // pass through loop condition
  cpd.transform(src, tgt, dummy, ns);
  constant_propagator_domaint &target_state=state_map[tgt]; // create
  target_state.merge(cpd, src, tgt);

  assert(state_map.size()==1 || state_map.size()==2);
  fixpoint_loop_body(loop, tgt, state_map);
  assert(!state_map.empty());

#ifdef DEBUG_VERBOSE
  output_state_map(std::cout, state_map);
  std::cout << "<<<<<<<<\n";
#endif
}

/*******************************************************************\

Function: unwind_boundst::fixpoint_loop_body()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::fixpoint_loop_body(
  const locationt loop,
  const locationt body,
  state_mapt &state_map)
{
  assert(state_map.size()==1 || state_map.size()==2);
  assert(state_map.find(body)!=state_map.end());

#ifdef DEBUG_VERBOSE
  std::cout << "========\n";
  std::cout << "Fixpoint loop body entry state:\n";
  entry_state.output(std::cout, dummy, ns);
#endif

  const goto_programt &goto_program=get_goto_program(loop);

  const locationt exit=get_loop_exit(loop);

  location_sett working_set;
  assert(working_set.empty());
  working_set.insert(body);

  // do fixpoint
  while(!working_set.empty())
  {
    // get next element from working set
    location_sett::iterator it;
    it=working_set.begin();
    const locationt l=*it;
    working_set.erase(it);

    // starting state
    const constant_propagator_domaint &current_state=state_map[l];

    std::list<locationt> successors;
    goto_program.get_successors(l, successors);

    assert(successors.size()<=2);
    assert(!l->is_goto() || (!l->guard.is_true() || successors.size()==1));

    for(std::list<locationt>::const_iterator s_it=successors.begin();
        s_it!=successors.end(); s_it++)
    {
      const locationt to_l=*s_it;

      // ignore break edges (breaks in the goto program can result in
      // conditional gotos for code like "if (y) break"), and edges
      // resulting from return statements in the loop body
      if(to_l->location_number>=exit->location_number)
      {
        continue;
      }

      constant_propagator_domaint new_state=current_state; // copy

      // underapproximate function calls
      if(!l->is_function_call())
      {
        new_state.transform(l, to_l, dummy, ns);
      }
      else
      {
        // calls are not resolved in the goto progarm
        assert(successors.size()==1);
      }

      constant_propagator_domaint &target_state=state_map[to_l];
      bool changed;
      changed=target_state.merge(new_state, l, to_l);

      // the backedge is not inserted into the worklist
      if(to_l!=loop && changed)
        working_set.insert(to_l);
    }
  }

  assert(!state_map.empty());

#ifdef DEBUG_VERBOSE
  output_state_map(std::cout, state_map);
  std::cout << "<<<<<<<<\n";
#endif
}

/*******************************************************************\

Function: unwind_boundst::check_shape()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool unwind_boundst::check_shape(const locationt loop) const
{
  if(!loop->is_backwards_goto())
    return false;

  const locationt loop_head=get_loop_head(loop);

  if(loop_head==loop)
    return false;

  locationt next=loop_head;
  next++;

  const locationt loop_exit=get_loop_exit(loop);

#if 0
  // this might happen for loops with a return in their body (goto to
  // END_FUNCTION), and inlined loops that had a return in their body
  // (jump to location after the inlined part)
  //
  // no jump out of the loop beyond the exit
  for(instructionst::const_iterator i_it=next;
      i_it!=loop; i_it++)
  {
    if(!i_it->is_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number<loop_head->location_number ||
       loop_exit->location_number<target->location_number)
      return false;
  }
#endif

  const goto_programt &goto_program=get_goto_program(loop);

  // no forward jump into the loop (except loop head)
  for(instructionst::const_iterator i_it=goto_program.instructions.begin();
      i_it!=loop_head; i_it++)
  {
    if(!i_it->is_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number>loop_head->location_number &&
       target->location_number<=loop->location_number)
      return false;
  }

#if 0
  // the inner and outer loop might have the same loop head
  //
  // no backward jump into the loop
  for(instructionst::const_iterator i_it=loop_exit;
      i_it!=goto_program.instructions.end(); i_it++)
  {
    if(!i_it->is_backwards_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number<=loop->location_number &&
       target->location_number>=loop_head->location_number)
      return false;
  }
#endif

#if 1
  // no backward jump into the loop
  for(instructionst::const_iterator i_it=loop_exit;
      i_it!=goto_program.instructions.end(); i_it++)
  {
    if(!i_it->is_backwards_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number<=loop->location_number &&
       target->location_number>loop_head->location_number)
      return false;
  }
#endif

  return true;
}

/*******************************************************************\

Function: unwind_boundst::handle_inner_loops()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::handle_inner_loops(
  const locationt loop,
  const state_mapt &state_map)
{
  const goto_programt &goto_program=get_goto_program(loop);

  assert(state_map.find(loop)!=state_map.end());
  const std::list<locationt> &inner_loops=inner_loop_map[loop];

  for(std::list<locationt>::const_iterator l_it=inner_loops.begin();
      l_it!=inner_loops.end(); l_it++)
  {
    const locationt inner_loop=*l_it;
    const locationt inner_loop_head=get_loop_head(inner_loop);

    // starting state for inner loop
    constant_propagator_domaint cpd;

    if(inner_loop_head==goto_program.instructions.begin())
    {
      cpd.make_top();
    }
    else
    {
#if 0
      locationt previous=inner_loop_head;
      previous--;

      if(state_map.find(previous)==state_map.end())
      {
        cpd.make_top();
      }
      else
      {
        cpd=state_map.at(previous); // copy
        cpd.transform(previous, inner_loop_head, dummy, ns);
      }
#endif

#if 1
      cpd.make_bottom();

      const std::set<goto_programt::targett> &incoming_edges
        =inner_loop_head->incoming_edges;
      assert(!incoming_edges.empty());

      for(std::set<goto_programt::targett>::const_iterator it
            =incoming_edges.begin();
          it!=incoming_edges.end(); it++)
      {
        const locationt l=*it;

        if(l==inner_loop)
          continue;

        constant_propagator_domaint tmp_cpd;
        state_mapt::const_iterator s_it=state_map.find(l);

        if(s_it==state_map.end())
        {
          tmp_cpd.make_top();
        }
        else
        {
          tmp_cpd=s_it->second;
        }

        tmp_cpd.transform(l, inner_loop_head, dummy, ns);
        cpd.merge(tmp_cpd, l, inner_loop_head);
      }
#endif
    }

    handle_loop(inner_loop, cpd);
  }
}

/*******************************************************************\

Function: unwind_boundst::handle_loop()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::handle_loop(
  const locationt loop,
  const constant_propagator_domaint &entry_state)
{
  assert(loop->is_goto());
  assert(loop->is_backwards_goto());
  assert(num_targets(loop)==1);

  if(!check_shape(loop))
  {
#ifdef DEBUG
    assert(false);
#endif
    return;
  }

  assert(check_shape(loop));
  assert(loop->is_backwards_goto());
  const locationt loop_head=get_loop_head(loop);

  int loop_counter=0;

  // entry state of next iteration
  constant_propagator_domaint next_entry_state=entry_state; // copy

  state_mapt state_map;
  assert(state_map.empty());

  // first unconditional iteration
  if(!cond_at_head(loop))
  {
    const locationt body=loop_head;
    state_map[body]=next_entry_state;
    assert(state_map.size()==1);

    fixpoint_loop_body(loop, body, state_map);

    // unconditional jump (e.g. break) out of the loop or infinite
    // inner loop; we ignore the inner loops in such cases
    if(state_map.find(loop)==state_map.end())
    {
      update_bound(loop, 1);
      return;
    }

    assert(state_map.find(loop)!=state_map.end());
    next_entry_state=state_map.at(loop);

    loop_counter++;

    // recursively handle inner loops
    if(dependent_loops)
    {
      handle_inner_loops(loop, state_map);
    }
  }

  while(true)
  {
    exprt cond=loop_cond(loop);
    next_entry_state.values.replace_const.replace(cond);
    cond=simplify_expr(cond, ns);

    bool c=cond.is_false();

    // handle condition
    if(c)
    {
      update_bound(loop, loop_counter);
      return;
    }

    assert(!c);
    loop_counter++;

    if(loop_counter>threshold)
    {
      max_bounds[loop]=-1;
      return;
    }

    state_map.clear();
    fixpoint_loop(loop, next_entry_state, state_map);

    if(state_map.find(loop)==state_map.end())
    {
      assert(loop_counter==1);
      update_bound(loop, 1);
      return;
    }

    assert(state_map.find(loop)!=state_map.end());
    next_entry_state=state_map.at(loop);

    // recursively handle inner loops
    if(dependent_loops)
    {
      handle_inner_loops(loop, state_map);
    }
  }
}

/*******************************************************************\

Function: unwind_boundst::compute_inner_loops()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::compute_inner_loops(
  const locationt loop, // outer loop
  const locationt loop_head) // outer loop head
{
  assert(loop->is_backwards_goto());
  assert(loop_head->location_number<loop->location_number);

  reverse_locationt start=forward_to_backward(loop);
  start++; // start one past the outer loop backward edge

  reverse_locationt stop=forward_to_backward(loop_head);
  stop++;

  for(reverse_locationt r_it=start; r_it!=stop; r_it++)
  {
    const locationt i_it=backward_to_forward(r_it);

    // potential inner loop
    if(i_it->is_backwards_goto())
    {
      const locationt inner_loop_head=get_loop_head(i_it);

      // contained
      if(loop_head->location_number<=inner_loop_head->location_number)
      {
        if(i_it!=inner_loop_head)
        {
          compute_inner_loops(i_it, inner_loop_head);
        }

        inner_loop_map[loop].push_front(i_it);
        outer_loops.erase(i_it);

        // continue past the inner loop head
        r_it=forward_to_backward(inner_loop_head);
      }
      else
      {
        assert(i_it!=inner_loop_head);
        compute_inner_loops(i_it, inner_loop_head);
      }
    }
  }
}

/*******************************************************************\

Function: unwind_boundst::update_loop_map()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::update_loop_map(const goto_programt &goto_program)
{
  assert(!goto_program.instructions.empty());

  for(reverse_locationt r_it=goto_program.instructions.crbegin();
      r_it!=goto_program.instructions.crend();
      r_it++)
  {
    const locationt i_it=backward_to_forward(r_it);

    if(i_it->is_backwards_goto())
    {
      const locationt loop_head=get_loop_head(i_it);
      assert(loop_head->location_number<=i_it->location_number);

      if(i_it!=loop_head)
      {
        compute_inner_loops(i_it, loop_head);

        // continue past loop head
        r_it=forward_to_backward(loop_head);
      }
    }
  }
}

/*******************************************************************\

Function: unwind_boundst::compute_loops()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::compute_loops()
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_backwards_goto())
      {
        all_loops.insert(i_it);
        outer_loops.insert(i_it); // we filter later
      }
    }

    // update loop info for this function
    update_loop_map(goto_program);
  }
}

/*******************************************************************\

Function: unwind_boundst::check_program()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::check_program() const
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_backwards_goto())
      {
        assert(i_it->is_goto());
      }

      if(i_it->is_goto())
      {
        assert(i_it->targets.size()==1);
      }
      else
      {
        assert(i_it->targets.size()==0);
      }
    }
  }
}

/*******************************************************************\

Function: unwind_boundst::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_boundst::operator()()
{
#ifdef DEBUG
  check_program();
#endif

  // get syntactical loops
  compute_loops();

#ifdef DEBUG
  output_outer_loops(std::cout);
  output_inner_loop_map(std::cout);
#endif

  // compute entry states for loops
  ait<constant_propagator_domaint> cp;
  cp(goto_functions, ns);

#ifdef DEBUG
  goto_functions.output(ns, std::cout);
  cp.output(ns, goto_functions, std::cout);
#endif

  const loop_sett &loops=dependent_loops?outer_loops:all_loops;

  // handle loops
  for(loop_sett::const_iterator l_it=loops.begin();
      l_it!=loops.end(); l_it++)
  {
    const locationt loop=*l_it;

    assert(loop->is_backwards_goto());

    const goto_programt &goto_program=get_goto_program(loop);

    const locationt loop_head=get_loop_head(loop);

    constant_propagator_domaint cpd;

    if(loop_head==goto_program.instructions.begin())
    {
      // use top
      cpd.make_top();
    }
    else
    {
#if 0
      // use state before loop head as the state at the head was
      // already merged with the state coming from the back edge
      locationt previous=loop_head;
      previous--;

      cpd=cp[previous];
      cpd.transform(previous, loop_head, dummy, ns);
#endif

#if 1
      // we use as the starting state the merge result of all
      // edges entering the loop head, except the backedge of
      // this loop

      cpd.make_bottom();

      const std::set<goto_programt::targett> &incoming_edges
        =loop_head->incoming_edges;
      assert(!incoming_edges.empty());

      for(std::set<goto_programt::targett>::const_iterator it
            =incoming_edges.begin();
          it!=incoming_edges.end(); it++)
      {
        const locationt l=*it;

        if(l==loop)
          continue;

        constant_propagator_domaint tmp_cpd=cp[l];
        tmp_cpd.transform(l, loop_head, dummy, ns);
        cpd.merge(tmp_cpd, l, loop_head);
      }
    }
#endif

#ifdef DEBUG
    std::cout << "Entry state:\n";
    cpd.output(std::cout, dummy, ns);
#endif

    handle_loop(loop, cpd);
  }
}
