/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation

#include "ai.h"

#include <cassert>
#include <memory>
#include <sstream>

#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_code.h>

#include "is_threaded.h"

void ai_baset::output(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  std::ostream &out) const
{
  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->second.body_available())
    {
      out << "////\n";
      out << "//// Function: " << f_it->first << "\n";
      out << "////\n";
      out << "\n";

      output(ns, f_it->second.body, f_it->first, out);
    }
  }
}

void ai_baset::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->source_location << "\n";

    abstract_state_before(i_it).output(out, *this, ns);
    out << "\n";
    #if 1
    goto_program.output_instruction(ns, identifier, out, *i_it);
    out << "\n";
    #endif
  }
}

/// Output the domains for the whole program as JSON
/// \par parameters: The namespace and goto_functions
/// \return The JSON object
jsont ai_baset::output_json(
  const namespacet &ns,
  const goto_functionst &goto_functions) const
{
  json_objectt result;

  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->second.body_available())
    {
      result[id2string(f_it->first)]=
        output_json(ns, f_it->second.body, f_it->first);
    }
    else
    {
      result[id2string(f_it->first)]=json_arrayt();
    }
  }

  return result;
}

/// Output the domains for a single function as JSON
/// \par parameters: The namespace, goto_program and it's identifier
/// \return The JSON object
jsont ai_baset::output_json(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier) const
{
  json_arrayt contents;

  forall_goto_program_instructions(i_it, goto_program)
  {
    json_objectt location;
    location["locationNumber"]=
      json_numbert(std::to_string(i_it->location_number));
    location["sourceLocation"]=
      json_stringt(i_it->source_location.as_string());
    location["abstractState"]=abstract_state_before(i_it).output_json(*this, ns);

    // Ideally we need output_instruction_json
    std::ostringstream out;
    goto_program.output_instruction(ns, identifier, out, *i_it);
    location["instruction"]=json_stringt(out.str());

    contents.push_back(location);
  }

  return contents;
}

/// Output the domains for the whole program as XML
/// \par parameters: The namespace and goto_functions
/// \return The XML object
xmlt ai_baset::output_xml(
  const namespacet &ns,
  const goto_functionst &goto_functions) const
{
  xmlt program("program");

  forall_goto_functions(f_it, goto_functions)
  {
    xmlt function("function");
    function.set_attribute("name", id2string(f_it->first));
    function.set_attribute(
      "body_available",
      f_it->second.body_available() ? "true" : "false");

    if(f_it->second.body_available())
    {
      function.new_element(output_xml(ns, f_it->second.body, f_it->first));
    }

    program.new_element(function);
  }

  return program;
}

/// Output the domains for a single function as XML
/// \par parameters: The namespace, goto_program and it's identifier
/// \return The XML object
xmlt ai_baset::output_xml(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier) const
{
  xmlt function_body;

  forall_goto_program_instructions(i_it, goto_program)
  {
    xmlt location;
    location.set_attribute(
      "location_number",
      std::to_string(i_it->location_number));
    location.set_attribute(
      "source_location",
      i_it->source_location.as_string());

    location.new_element(abstract_state_before(i_it).output_xml(*this, ns));

    // Ideally we need output_instruction_xml
    std::ostringstream out;
    goto_program.output_instruction(ns, identifier, out, *i_it);
    location.set_attribute("instruction", out.str());

    function_body.new_element(location);
  }

  return function_body;
}

void ai_baset::entry_state(const goto_functionst &goto_functions)
{
  // find the 'entry function'

  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it!=goto_functions.function_map.end())
    entry_state(f_it->second.body);
}

void ai_baset::entry_state(const goto_programt &goto_program)
{
  // The first instruction of 'goto_program' is the entry point with no history
  get_state(start_history(goto_program.instructions.begin())).make_entry();
}

void ai_baset::initialize(const goto_functionst::goto_functiont &goto_function)
{
  initialize(goto_function.body);
}

void ai_baset::initialize(const goto_programt &goto_program)
{
  // Domains are created and set to bottom on access.
  // So we do not need to set them to be bottom before hand.
#ifdef REMOVE_BEFORE_COMMIT
  // we mark everything as unreachable as starting point

  forall_goto_program_instructions(i_it, goto_program)
    get_state(i_it).make_bottom();
#endif
}

void ai_baset::initialize(const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    initialize(it->second);
}

void ai_baset::finalize()
{
  // Nothing to do per default
}

const tracet & ai_baset::get_next(
  working_sett &working_set)
{
  PRECONDITION(!working_set.empty());

#error "change to set"
  const tracet &h=working_set.pop();

  return h;
}

bool ai_baset::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  working_sett working_set;

  // Put the first location in the working set
  if(!goto_program.empty())
    put_in_working_set(
      working_set,
      start_history(goto_program.instructions.begin()));

  bool new_data=false;

  while(!working_set.empty())
  {
    const tracet h=get_next(working_set);

    if(visit(h, working_set, goto_program, goto_functions, ns))
      new_data=true;
  }

  return new_data;
}

bool ai_baset::visit(
  const tracet &h,
  working_sett &working_set,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  bool new_data=false;

  statet &current=get_state(h);
  locationt l=h.current_instruction_pointer();
  
  for(const auto &to_l : goto_program.get_successors(l))
  {
    if(to_l==goto_program.instructions.end())
      continue;

    // Let's make history
    const tracet &to_h=step(h, to_l);
    
    std::unique_ptr<statet> tmp_state(
      make_temporary_state(current));

    statet &new_values=*tmp_state;

    bool have_new_values=false;

    if(l->is_function_call() &&
       !goto_functions.function_map.empty())
    {
      // this is a big special case
      const code_function_callt &code=
        to_code_function_call(l->code);

      #warning "throws away history from called function"
      if(do_function_call_rec(
          h, to_h,
          code.function(),
          code.arguments(),
          goto_functions, ns))
        have_new_values=true;
    }
    else
    {
      // initialize state, if necessary
      get_state(to_h);

      #warning "convert transform signature"
      new_values.transform(
        h.current_instruction_pointer(),
        to_h.current_instruction_pointer(),
        *this,
        ns);

      if(merge(new_values, h, to_h))
        have_new_values=true;
    }

    if(have_new_values)
    {
      new_data=true;
      put_in_working_set(working_set, to_h);
    }
  }

  return new_data;
}

/// Remember that h_call and h_return are both in the caller
bool ai_baset::do_function_call(
  const tracet &h_call,
  const tracet &h_return,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  // initialize state, if necessary
  get_state(h_return);

  const goto_functionst::goto_functiont &goto_function=
    f_it->second;

  if(!goto_function.body_available())
  {
    // if we don't have a body, we just do an edge call -> return
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(h_call)));
    #warning "convert transform signature"
    tmp_state->transform(
      h_call.current_instruction_pointer(),
      h_return.current_instruction_pointer(),
      *this,
      ns);

    return merge(*tmp_state, h_call, h_return);
  }

  INVARIANT(!goto_function.body.instructions.empty(), "Have checked body_available()");

  // This is the edge from call site to function head.

  {
    // get the state at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();
    const tracet &h_begin=step(h_call, l_begin);
    
    // initialize state, if necessary
    get_state(h_begin);

    // do the edge from the call site to the beginning of the function
    std::unique_ptr<statet> tmp_state(make_temporary_state(get_state(h_call)));
    #warning "convert transform signature"
    tmp_state->transform(
      h_call.current_instruction_pointer(),
      h_begin.current_instruction_pointer(),
      *this,
      ns);

    bool new_data=false;

    // merge the new stuff
    if(merge(*tmp_state, h_call, h_begin))
      new_data=true;

    // do we need to do/re-do the fixedpoint of the body?
    if(new_data)
      fixedpoint(goto_function.body, goto_functions, ns);
    #error "doesn't have the info from h_begin"
  }

  // This is the edge from function end to return site.

  {
#error "unfinished"
    // get location at end of the procedure we have called
    locationt l_end=--goto_function.body.instructions.end();
    DATA_INVARIANT(
      l_end->is_end_function(),
      "the last instruction must be end_function");

    // do edge from end of function to instruction after call
    const statet &end_state=get_state(h_end);

    if(end_state.is_bottom())
      return false; // function exit point not reachable

    std::unique_ptr<statet> tmp_state(make_temporary_state(end_state));
    #warning "convert transform signature"
    tmp_state->transform(
      h_end.current_instruction_pointer(),
      h_return.current_instruction_pointer(),
      *this,
      ns);

    // Propagate those
    return merge(*tmp_state, h_end, h_return);
  }
}

bool ai_baset::do_function_call_rec(
  const tracet &h_call, const tracet &h_return,
  const exprt &function,
  const exprt::operandst &arguments,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  PRECONDITION(!goto_functions.function_map.empty());

  // We can't really do this here -- we rely on
  // these being removed by some previous analysis.
  PRECONDIITION(function.id()!=ID_dereference);

  // Can't be a function
  DATA_INVARIANT(function.id()!="NULL-object");
  DATA_INVARIANT(function.id()!=ID_member);
  DATA_INVARIANT(function.id()!=ID_index);
    
  bool new_data=false;

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier=function.get(ID_identifier);

    goto_functionst::function_mapt::const_iterator it=
      goto_functions.function_map.find(identifier);

    if(it==goto_functions.function_map.end())
      throw "failed to find function "+id2string(identifier);

    new_data=do_function_call(
      h_call, h_return,
      goto_functions,
      it,
      arguments,
      ns);
  }
  else if(function.id()==ID_if)
  {
    DATA_INVARIANT(function.operands().size()!=3, "if has three operands");

    bool new_data1=
      do_function_call_rec(
        h_call, h_return,
        function.op1(),
        arguments,
        goto_functions,
        ns);

    bool new_data2=
      do_function_call_rec(
        h_call, h_return,
        function.op2(),
        arguments,
        goto_functions,
        ns);

    if(new_data1 || new_data2)
      new_data=true;
  }
  else
  {
    throw "unexpected function_call argument: "+
      function.id_string();
  }

  return new_data;
}

void ai_baset::sequential_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(f_it!=goto_functions.function_map.end())
    fixedpoint(f_it->second.body, goto_functions, ns);
}

#error "Unfinished"
void ai_baset::concurrent_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  sequential_fixedpoint(goto_functions, ns);

  is_threadedt is_threaded(goto_functions);

  // construct an initial shared state collecting the results of all
  // functions
  goto_programt tmp;
  tmp.add_instruction();
  goto_programt::const_targett sh_target=tmp.instructions.begin();
  statet &shared_state=get_state(sh_target);

  typedef std::list<std::pair<goto_programt const*,
                              goto_programt::const_targett> > thread_wlt;
  thread_wlt thread_wl;

  forall_goto_functions(it, goto_functions)
    forall_goto_program_instructions(t_it, it->second.body)
    {
      if(is_threaded(t_it))
      {
        thread_wl.push_back(std::make_pair(&(it->second.body), t_it));

        goto_programt::const_targett l_end=
          it->second.body.instructions.end();
        --l_end;

        merge_shared(shared_state, l_end, sh_target, ns);
      }
    }

  // now feed in the shared state into all concurrently executing
  // functions, and iterate until the shared state stabilizes
  bool new_shared=true;
  while(new_shared)
  {
    new_shared=false;

    for(const auto &wl_pair : thread_wl)
    {
      working_sett working_set;
      put_in_working_set(working_set, wl_pair.second);

      statet &begin_state=get_state(wl_pair.second);
      merge(begin_state, sh_target, wl_pair.second);

      while(!working_set.empty())
      {
        goto_programt::const_targett l=get_next(working_set);

        visit(l, working_set, *(wl_pair.first), goto_functions, ns);

        // the underlying domain must make sure that the final state
        // carries all possible values; otherwise we would need to
        // merge over each and every state
        if(l->is_end_function())
          new_shared|=merge_shared(shared_state, l, sh_target, ns);
      }
    }
  }
}
