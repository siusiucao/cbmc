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

  /// Accessing individual domains at particular domains
  /// (without needing to know what kind of domain or history is used)
  /// A pointer to a copy as the method should be const and
  /// there are some non-trivial cases including merging domains, etc.

  /// Returns the abstract state before the given instruction
  /// PRECONDITION(l is dereferenceable)
  virtual std::unique_ptr<statet> abstract_state_before(locationt l) const = 0;

  /// Returns the abstract state after the given instruction
  virtual std::unique_ptr<statet> abstract_state_after(locationt l) const
  {
    /// PRECONDITION(l is dereferenceable && std::next(l) is dereferenceable)
    /// Check relies on a DATA_INVARIANT of goto_programs
    INVARIANT(!l->is_end_function(), "No state after the last instruction");
    return abstract_state_before(std::next(l));
  }

  /// Resets the domain
  virtual void clear()
  {
    call_sites.clear();
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


  // the work-queue is sorted using the history's less operator
  // all pointers are to objects stored in the history_map
  typedef std::set<const tracet *> working_sett;

  const tracet & get_next(working_sett &working_set);

  void put_in_working_set(
    working_sett &working_set,
    const tracet &h)
  {
    working_set.insert(&h);
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

  // Visit performs one step of abstract interpretation from history h
  // Depending on the instruction type it may compute a number of "edges"
  // or applications of the abstract transformer
  // true = found something new
  bool visit(
    const tracet &h,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  // The most basic step, computing one edge / transformer application.
  bool compute_edge(
    const tracet &h,
    working_sett &working_set,
    const locationt &to_l,
    const namespacet &ns);

  // function calls
  typedef std::map<irep_idt, std::set<locationt> > call_sitest;
  call_sitest call_sites;

  bool do_function_call_rec(
    const tracet &h_call,
    working_sett &working_set,
    const exprt &function,
    const exprt::operandst &arguments,
    const goto_functionst &goto_functions,
    const namespacet &ns);

  bool do_function_call(
    const tracet &h_call,
    working_sett &working_set,
    const goto_functionst &goto_functions,
    const goto_functionst::function_mapt::const_iterator f_it,
    const exprt::operandst &arguments,
    const namespacet &ns);

  bool do_function_return(
   const tracet &h_end,
   working_sett &working_set,
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
  virtual const tracet *step(const tracet &t, locationt to_l) = 0;
  virtual working_sett get_history(locationt &l) = 0;
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

  typedef std::set<historyT> location_historyt;
  // constructor
  ai_storaget():ai_baset()
  {
  }


  /// Direct access to the state map
  /// Unlike abstract_state_* this requires/has knowledge of the template types
  domainT &operator[](const historyT &h)
  {
    return static_cast<domainT &>(get_state(h));
  }

  const domainT &operator[](const historyT &h) const
  {
    return static_cast<const domainT &>(find_state(h));
  }

  void clear() override
  {
    history_map.clear();
    ai_baset::clear();
  }

  virtual working_sett get_history(locationt &l) override
  {
#warning "fix ugly type conversion"
    // This is ugly because there is no coversion from
    //  set<histortyT> -> set<const tracet *>
    working_sett res;
    for(const auto &h : history_map[l])
    {
      res.insert(&h);
    }
    return res;
  }

protected:

  /// Implement the type-specific methods that ai_baset delegates.
  /// Storage and access of domains is done by child classes.

  bool merge(const statet &src, const tracet &from, const tracet &to) override
  {
    statet &dest=get_state(to);
    return static_cast<domainT &>(dest).merge(
      static_cast<const domainT &>(src),
      from.current_location(),
      to.current_location());
    #warning "convert merge signature"
  }

  std::unique_ptr<statet> make_temporary_state(const statet &s) override
  {
    return util_make_unique<domainT>(static_cast<const domainT &>(s));
  }

  /// Record which histories have reached any particular point so that
  /// there is the option of merging with an existing one.
  typedef std::map<locationt, location_historyt> history_mapt;
  history_mapt history_map;

  const tracet & start_history(locationt bang) override
  {
    auto it=history_map[bang].insert(historyT(history_constructor_options, bang));
    return *it.first;
  }

  /// Returns a pointer as the history is allowed to prevent some steps.
  /// If it does, nullptr is returned.
  const tracet *step(const tracet &t, locationt to_l) override
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

// Ladies and gentlemen ... C++ ...
#define INHERITANCE_IS_HARD   typedef ai_storaget<historyT, domainT> parent; \
  using typename parent::tracet;                                        \
  using typename parent::statet;                                        \
  using typename parent::locationt;                                     \
  using typename parent::historyt;                                      \
  using typename parent::domaint;                                       \
  using typename parent::history_optionst;                              \
  using typename parent::domain_optionst;                               \
  using parent::domain_constructor_options


/// location_insensitive_ait stores one domain per function
template<typename historyT, typename domainT>
class location_insensitive_ait:public ai_storaget<historyT, domainT>
{
 public:
  INHERITANCE_IS_HARD;

  typedef std::map<irep_idt, domaint> state_mapt;

  location_insensitive_ait() : ai_storaget<domainT>() {}

  void clear() override
  {
    state_map.clear();
    parent::clear();
  }

  std::unique_ptr<statet> abstract_state_before(locationt t) const override
  {
    typename state_mapt::const_iterator it=state_map.find(t->function);
    if(it==state_map.end())
    {
      std::unique_ptr<statet> d = util_make_unique<domainT>();
      CHECK_RETURN(d->is_bottom());
      return d;
    }

    return util_make_unique<domainT>(it->second);
  }

  // Additional direct access operators
  using parent::operator[];
  domainT &operator[](const locationt &l)
  {
    return static_cast<domainT &>(get_state(l->function));
  }

  const domainT &operator[](const locationt &l) const
  {
    return static_cast<const domainT &>(find_state(l->function));
  }

  domainT &operator[](const irep_idt &f)
  {
    return static_cast<domainT &>(get_state(f));
  }

  const domainT &operator[](const irep_idt &f) const
  {
    return static_cast<const domainT &>(find_state(f));
  }


 protected :
  // this one creates states, if need be
  virtual statet &get_state(const irep_idt f)
  {
    typename state_mapt::iterator it=state_map.find(f);
    if(it==state_map.end())
    {
      it=state_map.insert(std::make_pair(f, domaint()));
      CHECK_RETURN(it->is_bottom());
    }

    return it->second;
  }

  virtual statet &get_state(const tracet &h) override
  {
    return get_state(h.current_location()->function);
  }


  // this one just finds states and can be used with a const ai_storage
  virtual const statet &find_state(const irep_idt f) const
  {
    typename state_mapt::const_iterator it=state_map.find(f);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }

  virtual const statet &find_state(const tracet &h) const override
  {
    return find_state(h.current_location()->function);
  }

 private:
  state_mapt state_map;
};


/// location_sensitive_ait stores one domain per location
template<typename historyT, typename domainT>
class location_sensitive_ait:public ai_storaget<historyT, domainT>
{
 public:
  INHERITANCE_IS_HARD;

  // It might be better to index on location number rather than locationt
  typedef std::map<locationt, domaint> state_mapt;

  location_sensitive_ait() : ai_storaget<domainT>() {}

  void clear() override
  {
    state_map.clear();
    parent::clear();
  }

  std::unique_ptr<statet> abstract_state_before(locationt t) const override
  {
    typename state_mapt::const_iterator it=state_map.find(t);
    if(it==state_map.end())
    {
      std::unique_ptr<statet> d = util_make_unique<domainT>();
      CHECK_RETURN(d->is_bottom());
      return d;
    }

    return util_make_unique<domainT>(it->second);
  }

  // Additional direct access operators
  using parent::operator[];
  domainT &operator[](const locationt &l)
  {
    return static_cast<domainT &>(get_state(l));
  }

  const domainT &operator[](const locationt &l) const
  {
    return static_cast<const domainT &>(find_state(l));
  }


 protected :
  // this one creates states, if need be
  virtual statet &get_state(locationt l)
  {
    typename state_mapt::iterator it=state_map.find(l);

    if(it==state_map.end())
    {
      it=state_map.insert(std::make_pair(l, domaint())).first;
      CHECK_RETURN(it->second.is_bottom());
    }

    return it->second;
  }

  virtual statet &get_state(const tracet &h) override
  {
    return get_state(h.current_location());
  }

  // this one just finds states and can be used with a const ai_storage
  virtual const statet &find_state(locationt l) const
  {
    typename state_mapt::const_iterator it=state_map.find(l);
    if(it==state_map.end())
      throw "failed to find state";

    return it->second;
  }

  virtual const statet &find_state(const tracet &h) const override
  {
    return find_state(h.current_location());
  }

  // FIXME : should be private
 protected:
  state_mapt state_map;
};


/// Connects up the methods for sequential analysis
/// aiT is expected to be derived from ai_baset
template<typename aiT>
class sequential_analysist:public aiT
{
public:
  using typename aiT::statet;
  using typename aiT::locationt;

  // constructors
  using aiT::aiT;

protected:
  void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns) override
  {
    this->sequential_fixedpoint(goto_functions, ns);
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
  using typename aiT::statet;
  using typename aiT::locationt;
  using typename aiT::domaint;

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
class ait:public sequential_analysist<location_sensitive_ait<ahistoricalt, domainT> >
{
  typedef sequential_analysist<location_sensitive_ait<ahistoricalt, domainT> > parent;
public:
  /// Inherit constructors
  using parent::parent;
};

/// concurrency_aware_ait : concurrent, location sensitive, history in-sensitive analysis
template<typename domainT>
class concurrency_aware_ait:public concurrent_analysist<location_sensitive_ait<ahistoricalt, domainT> >
{
  typedef concurrent_analysist<location_sensitive_ait<ahistoricalt, domainT> > parent;
public:
  /// Inherit constructors
  using parent::parent;
};

#endif // CPROVER_ANALYSES_AI_H
