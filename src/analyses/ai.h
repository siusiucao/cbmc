/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation

#ifndef CPROVER_ANALYSES_AI_H
#define CPROVER_ANALYSES_AI_H

#include <iosfwd>
#include <map>
#include <memory>

#include <util/json.h>
#include <util/xml.h>
#include <util/expr.h>
#include <util/make_unique.h>

#include <goto-programs/goto_model.h>

#include "ai_history.h"
#include "ai_domain.h"


/// The basic interface of an abstract interpreter.  This should be enough
/// to create, run and query an abstract interpreter.  It delegates everything
/// specific to the particular history or domain to subclasses.
// don't use me -- I am just a base class
// use ait instead
class ai_baset
{
public:
  typedef ai_history_baset tracet;
  typedef ai_domain_baset statet;
  typedef goto_programt::const_targett locationt;
  
  ai_baset()
  {
  }

  virtual ~ai_baset()
  {
  }

  /// Running the interpretter
  void operator()(
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_program);
    entry_state(goto_program);
    fixedpoint(goto_program, goto_functions, ns);
    finalize();
  }

  void operator()(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    initialize(goto_functions);
    entry_state(goto_functions);
    fixedpoint(goto_functions, ns);
    finalize();
  }

  void operator()(const goto_modelt &goto_model)
  {
    const namespacet ns(goto_model.symbol_table);
    initialize(goto_model.goto_functions);
    entry_state(goto_model.goto_functions);
    fixedpoint(goto_model.goto_functions, ns);
    finalize();
  }

  void operator()(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    goto_functionst goto_functions;
    initialize(goto_function);
    entry_state(goto_function.body);
    fixedpoint(goto_function.body, goto_functions, ns);
    finalize();
  }

  /// Resets the domain
  virtual void clear()
  {
    /// Empty as all storage and state is delegated
  }

  
  /// Accessing individual domains
  /// Returns the abstract state before the given instruction
  /// PRECONDITION(l is dereferenceable)
  virtual const statet & abstract_state_before(locationt l) const = 0
  #warning "may have to change to return an object, not a reference maybe even a pointer to a copy"

  /// Returns the abstract state after the given instruction
  virtual const statet & abstract_state_after(locationt l) const
  {
    /// PRECONDITION(l is dereferenceable && std::next(l) is dereferenceable)
    /// Check relies on a DATA_INVARIANT of goto_programs
    INVARIANT(!l->type.is_end_function(), "No state after the last instruction");
    return abstract_state_before(std::next(l));
  }


  virtual void output(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    std::ostream &out) const;

  void output(
    const goto_modelt &goto_model,
    std::ostream &out) const
  {
    const namespacet ns(goto_model.symbol_table);
    output(ns, goto_model.goto_functions, out);
  }

  void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    std::ostream &out) const
  {
    output(ns, goto_program, "", out);
  }

  void output(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function,
    std::ostream &out) const
  {
    output(ns, goto_function.body, "", out);
  }


  virtual jsont output_json(
    const namespacet &ns,
    const goto_functionst &goto_functions) const;

  jsont output_json(
    const goto_modelt &goto_model) const
  {
    const namespacet ns(goto_model.symbol_table);
    return output_json(ns, goto_model.goto_functions);
  }

  jsont output_json(
    const namespacet &ns,
    const goto_programt &goto_program) const
  {
    return output_json(ns, goto_program, "");
  }

  jsont output_json(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_json(ns, goto_function.body, "");
  }


  virtual xmlt output_xml(
    const namespacet &ns,
    const goto_functionst &goto_functions) const;

  xmlt output_xml(
    const goto_modelt &goto_model) const
  {
    const namespacet ns(goto_model.symbol_table);
    return output_xml(ns, goto_model.goto_functions);
  }

  xmlt output_xml(
    const namespacet &ns,
    const goto_programt &goto_program) const
  {
    return output_xml(ns, goto_program, "");
  }

  xmlt output_xml(
    const namespacet &ns,
    const goto_functionst::goto_functiont &goto_function) const
  {
    return output_xml(ns, goto_function.body, "");
  }

protected:
  // overload to add a factory
  virtual void initialize(const goto_programt &);
  virtual void initialize(const goto_functionst::goto_functiont &);
  virtual void initialize(const goto_functionst &);

  // override to add a cleanup step after fixedpoint has run
  virtual void finalize();

  void entry_state(const goto_programt &);
  void entry_state(const goto_functionst &);

  virtual void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const;

  virtual jsont output_json(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier) const;

  virtual xmlt output_xml(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier) const;


  // the work-queue is sorted by location number
  typedef std::set<const tracet &> working_sett;
  
  const tracet & get_next(working_sett &working_set);

  void put_in_working_set(
    working_sett &working_set,
    const tracet &h)
  {
    #error "change to set"
    working_set.push_back(h);
    return;
  }

  // true = found something new
  bool fixedpoint(
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  virtual void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns)=0;

  void sequential_fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns);
  void concurrent_fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // true = found something new
  bool visit(
    const tracet &h,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // function calls
  bool do_function_call_rec(
    const tracet &h_call, const tracet &h_return,
    const exprt &function,
    const exprt::operandst &arguments,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  bool do_function_call(
    const tracet &h_call, const tracet &h_return,
    const goto_functionst &goto_functions,
    const goto_functionst::function_mapt::const_iterator f_it,
    const exprt::operandst &arguments,
    const namespacet &ns);

  // abstract methods
  // These delegate anything that requires knowing the actual type of
  // the tracet or statet (as opposed to their parent class / interface).

  virtual bool merge(const statet &src, const tracet &from, const tracet &to)=0;
  // for concurrent fixedpoint
  virtual bool merge_shared(
    const statet &src,
    locationt from,
    locationt to,
    const namespacet &ns)=0;
  virtual statet &get_state(const tracet &h)=0;
  virtual const statet &find_state(const tracet &h) const=0;
  virtual std::unique_ptr<statet> make_temporary_state(const statet &s)=0;
  virtual const tracet &start_history(locationt bang) = 0;
};


/// Creation, storage and other operations dependent
/// on the exact types of abstraction used
/// historyT is expected to be derived from ai_history_baset (a.k.a. historyt)
/// domainT is expected to be derived from ai_domain_baset (a.k.a. domaint)
template<typename historyT, typename domainT>
class ai_storaget:public ai_baset
{
public:
  typedef historyT historyt;
  typedef domainT domaint;
  typedef historyt::history_optionst history_optionst;
  typedef domaint::domain_optionst domain_optionst;

protected:
  history_optionst history_constuctor_options;
  domain_optionst domain_constructor_options;
  
public:
  // constructor
  ai_storaget():
  history_constructor_options(),domain_constructor_options(), ai_baset()
  {
  }

  ai_storaget(const history_optionst &ho, const domain_optionst &do):
  history_constructor_options(ho), domain_constructor_options(do), ai_baset()
  {
  }

  /// Direct access to the state map
  domainT &operator[](const historyT &h)
  {
    return get_state(h);
  }

  const domainT &operator[](const historyT &h) const
  {
    return find_state(h);
  }


protected:

  /// Implement the type-specific methods that ai_baset delegates.
  /// Storage and access of domains is done by child classes.

  bool merge(const statet &src, const tracet &from, const tracet &to) override
  {
    statet &dest=get_state(to);
    return static_cast<domainT &>(dest).merge(
      static_cast<const domainT &>(src),
      from.current_instruction_pointer(),
      to.current_instruction_pointer());
    #warning "convert merge signature"
  }

  std::unique_ptr<statet> make_temporary_state(const statet &s) override
  {
    return util_make_unique<domainT>(static_cast<const domainT &>(s));
  }

  
  std::map<locationt, std::set<historyT> > history_map;
  
  const tracet & start_history(locationt bang) override
  {
    auto it=history_map.insert(historyT(history_constructor_options, bang));
    return *it;
  }

  const tracet &step(const trace &t, locationt to_l) override
  {
    return static_cast<const historyT &>(t).step(to_l, history_map[to_l]);
  }
    
private:
  // to enforce that domainT is derived from ai_domain_baset
  void dummy(const domainT &s) { const statet &x=s; (void)x; }

  // to enforce that historyT is derived from ai_history_baset
  void dummy(const historyT &h) { const tracet &x=h; (void)x; }
};


/// There are several different options of what kind of storage is used for
/// the domains and how historys map to domains.

template<typename historyT, typename domainT>
class location_insensitive_ait:public ai_storage<historyT, domainT>
{
 public:
  using ai_storage<historyT, domainT>::ai_storage;

  void clear() override
  {
    state_map.clear();
    ai_storage<historyT, domainT>::clear();
  }

  const statet & abstract_state_before(locationt t) const override
  {
    typename state_mapt::const_iterator it=state_map.find(t->function);
    if(it==state_map.end())
    {
      domaint d(domain_constructor_options);
      d.make_bottom();
      return d;
      #warning "suspect..."
    }

    return it->second;
  }

 protected :
  // this one creates states, if need be
  virtual statet &get_state(const tracet &h) override
  {
    locationt l=h.current_instruction_location();
    typename state_mapt::iterator it=state_map.find(l->function);

    if(it==state_map.end())
    {
      it=state_map.insert(l->function, domaint(domain_constructor_options) );
      it->second.make_bottom();  // Should be ensured by the domain constructor
    }
    
    return it->second;
  }

  // this one just finds states and can be used with a const ai_storage
  const statet &find_state(const tracet &l) const override
  {
    locationt l=h.current_instruction_location();
    typename state_mapt::const_iterator it=state_map.find(l->function);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }
  
 private:
  typedef std::unordered_map<irep_idt, domaint> state_mapt;
  state_mapt state_map;
};


template<typename historyT, typename domainT>
class location_sensitive_ait:public ai_storage<historyT, domainT>
{
 public:
  using ai_storage<historyT, domainT>::ai_storage;

  void clear() override
  {
    state_map.clear();
    ai_storage<historyT, domainT>::clear();
  }

  const statet & abstract_state_before(locationt t) const override
  {
    typename state_mapt::const_iterator it=state_map.find(t);
    if(it==state_map.end())
    {
      domaint d(domain_constructor_options);
      d.make_bottom();
      return d;
      #warning "suspect..."
    }

    return it->second;
  }

 protected :
  // this one creates states, if need be
  virtual statet &get_state(const tracet &h) override
  {
    locationt l=h.current_instruction_location();
    typename state_mapt::iterator it=state_map.find(l);

    if(it==state_map.end())
    {
      it=state_map.insert(l, domaint(domain_constructor_options) );
      it->second.make_bottom();  // Should be ensured by the domain constructor
    }
    
    return it->second;
  }

  // this one just finds states and can be used with a const ai_storage
  const statet &find_state(const tracet &h) const override
  {
    locationt l=h.current_instruction_location();
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }
  
 private:
  #warning "should this be location number?"
  typedef std::unordered_map<locationt, domaint> state_mapt;
  state_mapt state_map;  
};


template<typename historyT, typename domainT>
class history_sensitive_ait:public ai_storage<historyT, domainT>
{
 public:
  using ai_storage<historyT, domainT>::ai_storage;

  void clear() override
  {
    state_map.clear();
    ai_storage<historyT, domainT>::clear();
  }

  /// Access to all histories that reach the given location
  const statet & abstract_state_before(locationt t) const override
  {
    #error "TODO"
    /*
     * 1. Use the locationt -> historyt map
     * 2. merge all domains of valid histories
     */
    
    return it->second;
  }

 protected :
  // this one creates states, if need be
  virtual statet &get_state(const tracet &h) override
  {
    typename state_mapt::iterator it=state_map.find(h);

    if(it==state_map.end())
    {
      it=state_map.insert(h, domaint(domain_constructor_options) );
      it->second.make_bottom();  // Should be ensured by the domain constructor
    }
    
    return it->second;
  }

  // this one just finds states and can be used with a const ai_storage
  const statet &find_state(const tracet &h) const override
  {
    typename state_mapt::const_iterator it=state_map.find(h);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }
  
 private:
  typedef std::unordered_map<historyt, domaint> state_mapt;
  state_mapt state_map;
};


/// Connects up the methods for sequential analysis
/// aiT is expected to be derived from ai_baset
template<typename aiT>
class sequential_analysist:public aiT
{
public:
  // constructors
  using aiT::aiT;
  
protected:
  void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns) override
  {
    sequential_fixedpoint(goto_functions, ns);
  }

private:
  // not implemented in sequential analyses
  bool merge_shared(
    const statet &src,
    locationt from,
    locationt to,
    const namespacet &ns) override
  {
    throw "not implemented";
  }

  // to enforce that aiT is derived from ai_baset
  void dummy(const aiT &a) { const ai_baset &x=a; (void)x; }
};


/// Connects up the methods for concurrent analysis
/// aiT is expected to be derived from ai_baset
template<typename aiT>
class concurrent_analysist:public aiT
{
public:
  // constructors
  using aiT::aiT;
  
  bool merge_shared(
    const statet &src,
    locationt from,
    locationt to,
    const namespacet &ns) override
  {
    statet &dest=this->get_state(to);
    return static_cast<domaint &>(dest).merge_shared(
      static_cast<const domaint &>(src), from, to, ns);
  }

protected:
  void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns) override
  {
    this->concurrent_fixedpoint(goto_functions, ns);
  }

 private:
  // to enforce that aiT is derived from ai_baset
  void dummy(const aiT &a) { const ai_baset &x=a; (void)x; }
};


/// Specific kinds of analyzer
/// Also examples of how to combine analysis type, history and domain.

/// ait : sequential, location sensitive, history in-sensitive analysis
/// domainT is expected to be derived from ai_domain_baseT
template<typename domainT>
class ait:public sequential_analysis<location_sensitive_ait<ahistorical, domainT> >
{
  typedef sequential_analysis<location_sensitive_ait<ahistorical, domainT> > parent;
public:
  /// Inherit constructors
  using parent::parent;
};

/// concurrency_aware_ait : concurrent, location sensitive, history in-sensitive analysis
template<typename domainT>
class concurrency_aware_ait:public concurrent_analysist<location_sensitive_ait<ahistorical, domainT> >
{
  typedef concurrent_analysist<location_sensitive_ait<ahistorical, domainT> > parent;
public:
  /// Inherit constructors
  using parent::parent;
};

#endif // CPROVER_ANALYSES_AI_H
