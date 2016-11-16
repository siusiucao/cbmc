/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS
#define CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS

#include <util/message.h>
#include <util/json.h>
#include <util/json_expr.h>
#include <util/i2string.h>

#include "goto_functions.h"

class goto_inlinet:public messaget
{
public:
  goto_inlinet(
    goto_functionst &goto_functions,
    const namespacet &ns,
    message_handlert &message_handler,
    bool adjust_function):
    messaget(message_handler),
    goto_functions(goto_functions),
    ns(ns),
    adjust_function(adjust_function)
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

  // call after goto_functions.update()!
  void show_inline_log(std::ostream &out)
  {
    inline_log.cleanup(cache);
    inline_log.show_inline_log(out);
  }

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

  class goto_inline_logt
  {
  public:
    class goto_inline_log_infot
    {
    public:
      // original segment location numbers
      unsigned begin_location_number;
      unsigned end_location_number;
      unsigned call_location_number; // original call location number
      irep_idt function; // function from which segment was inlined
      goto_programt::const_targett end; // segment end
    };

    // remove segment that refer to the given goto program
    void cleanup(const goto_programt &goto_program)
    {
      forall_goto_program_instructions(it, goto_program)
        log_map.erase(it);
    }

    void cleanup(const goto_functionst::function_mapt &function_map)
    {
      for(goto_functionst::function_mapt::const_iterator it
            =function_map.begin(); it!=function_map.end(); it++)
      {
        const goto_functiont &goto_function=it->second;

        if(!goto_function.body_available())
          continue;

        cleanup(goto_function.body);
      }
    }

    void add_segment(
      const goto_programt &goto_program,
      const unsigned begin_location_number,
      const unsigned end_location_number,
      const unsigned call_location_number,
      const irep_idt function)
    {
      assert(!goto_program.empty());
      assert(!function.empty());
      assert(end_location_number>=begin_location_number);

      goto_programt::const_targett start=goto_program.instructions.begin();
      assert(log_map.find(start)==log_map.end());

      goto_programt::const_targett end=goto_program.instructions.end();
      end--;

      goto_inline_log_infot info;
      info.begin_location_number=begin_location_number;
      info.end_location_number=end_location_number;
      info.call_location_number=call_location_number;
      info.function=function;
      info.end=end;

      log_map[start]=info;
    }

    void copy_from(const goto_programt &from, const goto_programt &to)
    {
      assert(from.instructions.size()==to.instructions.size());

      goto_programt::const_targett it1=from.instructions.begin();
      goto_programt::const_targett it2=to.instructions.begin();

      for(;it1!=from.instructions.end(); it1++, it2++)
      {
        assert(it2!=to.instructions.end());
        assert(it1->location_number==it2->location_number);

        log_mapt::const_iterator l_it=log_map.find(it1);
        if(l_it!=log_map.end())
        {
          assert(log_map.find(it2)==log_map.end());

          goto_inline_log_infot info=l_it->second;
          goto_programt::const_targett end=info.end;

          // find end of new
          goto_programt::const_targett tmp_it=it1;
          goto_programt::const_targett new_end=it2;
          while(tmp_it!=end)
          {
            new_end++;
            tmp_it++;
          }

          info.end=new_end;

          log_map[it2]=info;
        }
      }
    }

    // call after goto_functions.update()!
    void show_inline_log(std::ostream &out) const
    {
      json_objectt json_result;
      json_arrayt &json_inlined=json_result["inlined"].make_array();

      for(log_mapt::const_iterator it=log_map.begin();
          it!=log_map.end(); it++)
      {
        json_objectt &object=json_inlined.push_back().make_object();

        goto_programt::const_targett start=it->first;
        const goto_inline_log_infot &info=it->second;
        goto_programt::const_targett end=info.end;

        assert(start->location_number<=end->location_number);

        object["call"]=json_numbert(i2string(info.call_location_number));
        object["function"]=json_stringt(info.function.c_str());

        json_arrayt &json_orig=object["original_segment"].make_array();
        json_orig.push_back()=json_numbert(i2string(
          info.begin_location_number));
        json_orig.push_back()=json_numbert(i2string(
          info.end_location_number));

        json_arrayt &json_new=object["inlined_segment"].make_array();
        json_new.push_back()=json_numbert(i2string(start->location_number));
        json_new.push_back()=json_numbert(i2string(end->location_number));
      }

      out << json_result;
      out << "\n";
    }

    // map from segment start to inline info
    typedef std::map<
      goto_programt::const_targett,
      goto_inline_log_infot> log_mapt;

    log_mapt log_map;
  };

protected:
  goto_functionst &goto_functions;
  const namespacet &ns;
  
  const bool adjust_function;
  goto_inline_logt inline_log;

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
    const goto_programt::targett target,
    const irep_idt &function_name,
    const code_typet &code_type,
    const exprt::operandst &arguments,
    goto_programt &dest);

  void parameter_destruction(
    const goto_programt::targett target,
    const irep_idt &function_name,
    const code_typet &code_type,
    goto_programt &dest);

  // goto functions that were already inlined transitively
  typedef goto_functionst::function_mapt cachet;
  cachet cache;

  typedef hash_set_cont<irep_idt, irep_id_hash> finished_sett;
  finished_sett finished_set;

  typedef hash_set_cont<irep_idt, irep_id_hash> recursion_sett;
  recursion_sett recursion_set;
  
  typedef hash_set_cont<irep_idt, irep_id_hash> no_body_sett;
  no_body_sett no_body_set;
};

#endif
