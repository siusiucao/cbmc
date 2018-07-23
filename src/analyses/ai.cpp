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

    abstract_state_before(i_it)->output(out, *this, ns);
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
    location["abstractState"]=
      abstract_state_before(i_it)->output_json(*this, ns);

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

    location.new_element(abstract_state_before(i_it)->output_xml(*this, ns));

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
  const tracet &start=start_history(goto_program.instructions.begin());
  get_state(start).make_entry();
}

void ai_baset::initialize(const goto_functionst::goto_functiont &goto_function)
{
  initialize(goto_function.body);
}

void ai_baset::initialize(const goto_programt &goto_program)
{
  // Domains are created and set to bottom on access.
  // So we do not need to set them to be bottom before hand.
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

const ai_baset::tracet & ai_baset::get_next(
  working_sett &working_set)
{
  PRECONDITION(!working_set.empty());

  // STL guarantees this will be key minimal
  auto first=working_set.begin();

  const tracet *h=*first;

  working_set.erase(first);

  return *h;
}

bool ai_baset::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  working_sett working_set;

  // Put the first location in the working set
  if(!goto_program.empty())
  {
    locationt first=goto_program.instructions.begin();
    put_in_working_set(working_set, start_history(first));
  #warning "should only start history once?"

    call_sitest::mapped_type empty_set;
    call_sites.insert(std::make_pair(first->function, empty_set));
  }

  bool new_data=false;

  while(!working_set.empty())
  {
    const tracet &h=get_next(working_set);

    // goto_program is really only needed for iterator manipulation
    locationt l=h.current_location();
    auto it=goto_functions.function_map.find(l->function);

    DATA_INVARIANT(it!=goto_functions.function_map.end(),
                   "instruction.function must be a mapped function");
    DATA_INVARIANT(it->second.body_available(),
                   "instruction.function implies instruction is in function");

    if(visit(h, working_set, it->second.body, goto_functions, ns))
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

  locationt l=h.current_location();

  // Function call and return are special cases
  if(l->is_function_call() && !goto_functions.function_map.empty())
  {
    DATA_INVARIANT(goto_program.get_successors(l).size() == 1,
                   "function calls only have one successor...");
    DATA_INVARIANT(*(goto_program.get_successors(l).begin()) == std::next(l),
                   "... and it is the next instruction / return location");

    const code_function_callt &code = to_code_function_call(l->code);
    if(do_function_call_rec(
         h,
         working_set,
         code.function(),
         code.arguments(),
         goto_functions, ns))
      new_data=true;
  }
  else if (l->is_end_function())
  {
    DATA_INVARIANT(goto_program.get_successors(l).empty(),
                   "The end function instruction should have no successors.");

    if (do_function_return(h, working_set, ns))
      new_data=true;
  }
  else
  {
    // Successors can be empty, for example assume(0).
    // Successors can contain duplicates, for example GOTO next;
    for(const auto &to_l : goto_program.get_successors(l))
    {
      if(to_l==goto_program.instructions.end())
        continue;

      new_data |= compute_edge(h, working_set, to_l, ns);
    }
  }

  return new_data;
}

bool ai_baset::compute_edge(
  const tracet &h,
  working_sett &working_set,
  const locationt &to_l,
  const namespacet &ns)
{
  // Has history taught us not to step here...
  const tracet *next=step(h, to_l);
  if (next == nullptr)
    return false;
  const tracet &to_h=*next;

  // Abstract domains are mutable so we must copy before we transform
  statet &current=get_state(h);

  std::unique_ptr<statet> tmp_state(make_temporary_state(current));
  statet &new_values=*tmp_state;

  // Apply transformer
#warning "convert transform signature"
  new_values.transform(
    h.current_location(),
    to_h.current_location(),
    *this,
    ns);

  // Initialize state(s), if necessary
  get_state(to_h);

  if(merge(new_values, h, to_h))
  {
    put_in_working_set(working_set, to_h);
    return true;
  }

  return false;
}


/// Remember that h_call and h_return are both in the caller
bool ai_baset::do_function_call(
  const tracet &h_call,
  working_sett &working_set,
  const goto_functionst &goto_functions,
  const goto_functionst::function_mapt::const_iterator f_it,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  locationt l_call=h_call.current_location();
  PRECONDITION(l_call->is_function_call());

  const goto_functionst::goto_functiont &goto_function=
    f_it->second;

  locationt l_return = std::next(l_call);
  // DATA_INVARIANT(l_return.is_dereferenceable(),
  //                "CALL cannot be last instruction");

  if(!goto_function.body_available())
  {
    // If we don't have a body, we just do an edge call -> return
    // and we don't update the call_site map
    return compute_edge(h_call, working_set, l_return, ns);
  }
  else
  {
    // This is the edge from call site to function head.

    // Update the call map (so that the function can return here)
    bool new_call_site=call_sites[f_it->first].insert(l_call).second;

    // Get the location at the beginning of the function
    locationt l_begin=goto_function.body.instructions.begin();
    INVARIANT(l_begin != goto_function.body.instructions.end(),
              "Have checked body_available()");

    // Do the edge from the call site to the beginning of the function
    bool new_data=compute_edge(h_call, working_set, l_begin, ns);


    /* As the list of call sites is built incrementally, we have to be careful
     * to make sure that return values are correctly computed.
     * Once a call site is on the list then the next time the callee's
     * END_FUNCTION is reached it will update the call site.
     * However as histories and domains may merge, we cannot guarantee
     * when or even if the callee's END_FUNCTION will be reached next.
     * So when a new call site is added to the list we also need to
     * (pro-actively) merge the possible return states.
     */
    if(new_call_site)
    {
      // Find the end of the callee function
      locationt l_end=l_begin;
      for ( ; (!l_end->is_end_function()); l_end=std::next(l_end))
      {
        DATA_INVARIANT(
          l_end!=goto_function.body.instructions.end(),
          "Must reach and END_FUNCTION instruction before end() iterator");
        // Termination also guaranteed by a DATA_INVARIANT
      }

      // We want the return location, rather than the call site itself
      locationt l_return=std::next(l_call);

      for(const tracet *h : get_history(l_end))
      {
        const tracet &h_end=*h;
        const statet &end_state = get_state(h_end);

        // Can have histories with domains as bottom, for example
        // an infeasible branch to the end of the program.
        if(!end_state.is_bottom())
        {
          if(compute_edge(h_end, working_set, l_return, ns))
            new_data=true;
        }
      }
    }

    return new_data;
  }
  UNREACHABLE;
}

bool ai_baset::do_function_call_rec(
  const tracet &h_call,
  working_sett &working_set,
  const exprt &function,
  const exprt::operandst &arguments,
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  PRECONDITION(!goto_functions.function_map.empty());

  // We can't really do this here -- we rely on
  // these being removed by some previous analysis.
  PRECONDITION(function.id()!=ID_dereference);

  // Can't be a function
  DATA_INVARIANT(function.id()!="NULL-object", "Function cannot be null object");
  DATA_INVARIANT(function.id()!=ID_member, "Function cannot be struct field");
  DATA_INVARIANT(function.id()!=ID_index, "Function cannot be array element");

  bool new_data=false;

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(function).get_identifier();

    goto_functionst::function_mapt::const_iterator it=
      goto_functions.function_map.find(identifier);

    if(it==goto_functions.function_map.end())
      throw "failed to find function "+id2string(identifier);

    new_data=do_function_call(
      h_call,
      working_set,
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
        h_call,
        working_set,
        function.op1(),
        arguments,
        goto_functions,
        ns);

    bool new_data2=
      do_function_call_rec(
        h_call,
        working_set,
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

bool ai_baset::do_function_return(
  const tracet &h_end,
  working_sett &working_set,
  const namespacet &ns)
{
  bool new_data=false;

  locationt l_end=h_end.current_location();
  PRECONDITION(l_end->is_end_function());

  irep_idt function_name=l_end->function;

  auto it=call_sites.find(function_name);
  INVARIANT(
    it != call_sites.end(),
    "All functions analyzed should in call_sites map");

  // Note that it->second.empty() => is the entry function for the analysis
  // but not vica versa because recursion!
  for(const auto &l_call : it->second)
  {
    // We want the return location, rather than the call site itself
    locationt l_return=std::next(l_call);
    // DATA_INVARIANT(l_return.is_dereferenceable(),
    //                "last instruction must be END_FUNCTION, not call")

    if(compute_edge(h_end, working_set, l_return, ns))
    {
      new_data=true;
    }
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

#warning "Concurrent fixpoint is unfinished"
void ai_baset::concurrent_fixedpoint(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  sequential_fixedpoint(goto_functions, ns);

  is_threadedt is_threaded(goto_functions);

#if 0
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
  #endif
}
