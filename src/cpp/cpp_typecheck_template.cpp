/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/simplify_expr.h>

#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_declarator_converter.h"
#include "cpp_template_type.h"
#include "cpp_convert_type.h"
#include "cpp_template_args.h"

/*******************************************************************\

Function: cpp_typecheckt::salvage_default_arguments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::salvage_default_arguments(
  const template_typet &old_type,
  template_typet &new_type)
{
  const template_typet::template_parameterst &old_parameters=
    old_type.template_parameters();
  template_typet::template_parameterst &new_parameters=
    new_type.template_parameters();

  for(std::size_t i=0; i<new_parameters.size(); i++)
  {
    if(i<old_parameters.size() &&
       old_parameters[i].has_default_argument() &&
       !new_parameters[i].has_default_argument())
    {
      // TODO The default may depend on previous parameters!!
      new_parameters[i].default_argument()=old_parameters[i].default_argument();
    }
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_class_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_class_template(
  cpp_declarationt &declaration)
{
  // Do template parameters. This also sets up the template scope.
  cpp_scopet &template_scope=
    typecheck_template_parameters(declaration.template_type());

  typet &type=declaration.type();
  template_typet &template_type=declaration.template_type();

  bool has_body=type.find(ID_body).is_not_nil();

  const cpp_namet &cpp_name=
    static_cast<const cpp_namet &>(type.find(ID_tag));

  if(cpp_name.is_nil())
  {
    error().source_location=type.source_location();
    error() << "class templates must not be anonymous" << eom;
    throw 0;
  }

  if(!cpp_name.is_simple_name())
  {
    error().source_location=cpp_name.source_location();
    error() << "simple name expected as class template tag" << eom;
    throw 0;
  }

  irep_idt base_name=cpp_name.get_base_name();

  const cpp_template_args_non_tct &partial_specialization_args=
    declaration.partial_specialization_args();

  const irep_idt symbol_name=
    class_template_identifier(
      base_name, template_type, partial_specialization_args);

  #if 0
  // Check if the name is already used by a different template
  // in the same scope.
  {
    cpp_scopet::id_sett id_set;
    cpp_scopes.current_scope().lookup(
      base_name,
      cpp_scopet::SCOPE_ONLY,
      cpp_scopet::TEMPLATE,
      id_set);

    if(!id_set.empty())
    {
      const symbolt &previous=lookup((*id_set.begin())->identifier);
      if(previous.name!=symbol_name || id_set.size()>1)
      {
        error().source_location=cpp_name.source_location();
        str << "template declaration of `" << base_name.c_str()
            << " does not match previous declaration\n";
        str << "location of previous definition: " << previous.location;
        throw 0;
      }
    }
  }
  #endif

  // check if we have it already

  symbol_tablet::symbolst::iterator previous_symbol=
    symbol_table.symbols.find(symbol_name);

  if(previous_symbol!=symbol_table.symbols.end())
  {
    // there already
    cpp_declarationt &previous_declaration=
      to_cpp_declaration(previous_symbol->second.type);

    bool previous_has_body=
      previous_declaration.type().find(ID_body).is_not_nil();

    // check if we have 2 bodies
    if(has_body && previous_has_body)
    {
      error().source_location=cpp_name.source_location();
      error() << "template struct `" << base_name
              << "' defined previously\n"
              << "location of previous definition: "
              << previous_symbol->second.location << eom;
      throw 0;
    }

    if(has_body)
    {
      // We replace the template!
      // We have to retain any default parameters from the previous declaration.
      salvage_default_arguments(
        previous_declaration.template_type(),
        declaration.template_type());

      previous_symbol->second.type.swap(declaration);

      #if 0
      std::cout << "*****\n";
      std::cout << *cpp_scopes.id_map[symbol_name];
      std::cout << "*****\n";
      std::cout << "II: " << symbol_name << std::endl;
      #endif

      // We also replace the template scope (the old one could be deleted).
      cpp_scopes.id_map[symbol_name]=&template_scope;

      // We also fix the parent scope in order to see the new
      // template arguments
    }
    else
    {
      // just update any default arguments
      salvage_default_arguments(
        declaration.template_type(),
        previous_declaration.template_type());
    }

    ASSERT(cpp_scopes.id_map[symbol_name]->id_class == cpp_idt::TEMPLATE_SCOPE);
    return;
  }

  // it's not there yet

  symbolt symbol;

  symbol.name=symbol_name;
  symbol.base_name=base_name;
  symbol.location=cpp_name.source_location();
  symbol.mode=ID_cpp;
  symbol.module=module;
  symbol.type.swap(declaration);
  symbol.is_macro=false;
  symbol.value=exprt("template_decls");

  symbol.pretty_name=
    cpp_scopes.current_scope().prefix+id2string(symbol.base_name);

  symbolt *new_symbol;
  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::typecheck_compound_type: "
            << "symbol_table.move() failed"
            << eom;
    throw 0;
  }

  // put into current scope
  cpp_idt &id=cpp_scopes.put_into_scope(*new_symbol);
  id.id_class=cpp_idt::TEMPLATE;
  id.prefix=cpp_scopes.current_scope().prefix+
            id2string(new_symbol->base_name);

  // link the template symbol with the template scope
  cpp_scopes.id_map[symbol_name]=&template_scope;
  ASSERT(cpp_scopes.id_map[symbol_name]->id_class==cpp_idt::TEMPLATE_SCOPE);
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_function_template

  Inputs:

 Outputs:

 Purpose: typecheck function templates

\*******************************************************************/

void cpp_typecheckt::typecheck_function_template(
  cpp_declarationt &declaration)
{
  ASSERT(declaration.declarators().size()==1);

  cpp_declaratort &declarator=declaration.declarators()[0];
  const cpp_namet &cpp_name=to_cpp_name(declarator.add(ID_name));

  // do template arguments
  // this also sets up the template scope
  cpp_scopet &template_scope=
    typecheck_template_parameters(declaration.template_type());

  if(!cpp_name.is_simple_name())
  {
    error().source_location=declaration.source_location();
    error() << "function template must have simple name" << eom;
    throw 0;
  }

  irep_idt base_name=cpp_name.get_base_name();

  template_typet &template_type=declaration.template_type();

  typet function_type=
    declarator.merge_type(declaration.type());

  cpp_convert_plain_type(function_type);

  irep_idt symbol_name=
    function_template_identifier(
      base_name,
      template_type,
      function_type);

  bool has_value=declarator.find(ID_value).is_not_nil();

  // check if we have it already

  symbol_tablet::symbolst::iterator previous_symbol=
    symbol_table.symbols.find(symbol_name);

  if(previous_symbol!=symbol_table.symbols.end())
  {
    bool previous_has_value =
     to_cpp_declaration(previous_symbol->second.type).
       declarators()[0].find(ID_value).is_not_nil();

    if(has_value && previous_has_value)
    {
      error().source_location=cpp_name.source_location();
      error() << "function template symbol `" << base_name
              << "' declared previously\n"
              << "location of previous definition: "
              << previous_symbol->second.location << eom;
      throw 0;
    }

    if(has_value)
    {
      previous_symbol->second.type.swap(declaration);
      cpp_scopes.id_map[symbol_name]=&template_scope;
    }

    // todo: the old template scope now is useless,
    // and thus, we could delete it
    return;
  }

  symbolt symbol;
  symbol.name=symbol_name;
  symbol.base_name=base_name;
  symbol.location=cpp_name.source_location();
  symbol.mode=ID_cpp;
  symbol.module=module;
  symbol.value.make_nil();

  symbol.type.swap(declaration);
  symbol.pretty_name=
    cpp_scopes.current_scope().prefix+id2string(symbol.base_name);

  symbolt *new_symbol;
  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::typecheck_compound_type: "
            << "symbol_table.move() failed"
            << eom;
    throw 0;
  }

  // put into scope
  cpp_idt &id=cpp_scopes.put_into_scope(*new_symbol);
  id.id_class=cpp_idt::TEMPLATE;
  id.prefix=cpp_scopes.current_scope().prefix+
            id2string(new_symbol->base_name);

  // link the template symbol with the template scope
  ASSERT(template_scope.id_class==cpp_idt::TEMPLATE_SCOPE);
  cpp_scopes.id_map[symbol_name] = &template_scope;
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_class_template_member

  Inputs:

 Outputs:

 Purpose: typecheck class tempalte members;
          these can be methods or static members

\*******************************************************************/

void cpp_typecheckt::typecheck_class_template_member(
  cpp_declarationt &declaration)
{
  ASSERT(declaration.declarators().size()==1);

  cpp_declaratort &declarator=declaration.declarators()[0];
  const cpp_namet &cpp_name=to_cpp_name(declarator.add(ID_name));

  ASSERT(cpp_name.is_qualified() ||
         cpp_name.has_template_args());

  // must be of the form: name1<template_args>::name2
  // or:                  name1<template_args>::operator X
  if(cpp_name.get_sub().size()==4 &&
     cpp_name.get_sub()[0].id()==ID_name &&
     cpp_name.get_sub()[1].id()==ID_template_args &&
     cpp_name.get_sub()[2].id()=="::" &&
     cpp_name.get_sub()[3].id()==ID_name)
  {
  }
  else if(cpp_name.get_sub().size()==5 &&
          cpp_name.get_sub()[0].id()==ID_name &&
          cpp_name.get_sub()[1].id()==ID_template_args &&
          cpp_name.get_sub()[2].id()=="::" &&
          cpp_name.get_sub()[3].id()==ID_operator)
  {
  }
  else
  {
    return; // TODO
    error().source_location=cpp_name.source_location();
    error() << "bad template name" << eom;
    throw 0;
  }

  // let's find the class template this function template belongs to.
  cpp_scopet::id_sett id_set;

  cpp_scopes.current_scope().lookup(
    cpp_name.get_sub().front().get(ID_identifier),
    cpp_scopet::SCOPE_ONLY, // look only in current scope
    cpp_scopet::TEMPLATE,   // must be template
    id_set);

  if(id_set.empty())
  {
    error() << cpp_scopes.current_scope();
    error().source_location=cpp_name.source_location();
    error() << "class template `"
            << cpp_name.get_sub().front().get(ID_identifier)
            << "' not found" << eom;
    throw 0;
  }
  else if(id_set.size()>1)
  {
    error().source_location=cpp_name.source_location();
    error() << "class template `"
            << cpp_name.get_sub().front().get(ID_identifier)
            << "' is ambiguous" << eom;
    throw 0;
  }
  else if((*(id_set.begin()))->id_class!=cpp_idt::TEMPLATE)
  {
    // std::cerr << *(*id_set.begin()) << std::endl;
    error().source_location=cpp_name.source_location();
    error() << "class template `"
            << cpp_name.get_sub().front().get(ID_identifier)
            << "' is not a template" << eom;
    throw 0;
  }

  const cpp_idt &cpp_id=**(id_set.begin());
  symbolt &template_symbol=
    symbol_table.symbols.find(cpp_id.identifier)->second;

  exprt &template_methods=static_cast<exprt &>(
    template_symbol.value.add("template_methods"));

  template_methods.copy_to_operands(declaration);

  // save current scope
  cpp_save_scopet cpp_saved_scope(cpp_scopes);

  const irept &instantiated_with =
    template_symbol.value.add("instantiated_with");

  for(std::size_t i=0; i<instantiated_with.get_sub().size(); i++)
  {
    const cpp_template_args_tct &tc_template_args=
      static_cast<const cpp_template_args_tct &>(
        instantiated_with.get_sub()[i]);

    cpp_declarationt decl_tmp=declaration;

    // do template arguments
    // this also sets up the template scope of the method
    cpp_scopet &method_scope=
      typecheck_template_parameters(decl_tmp.template_type());

    cpp_scopes.go_to(method_scope);

    // mapping from template arguments to values/types
    template_map.build(decl_tmp.template_type(), tc_template_args);

    decl_tmp.remove(ID_template_type);
    decl_tmp.remove(ID_is_template);

    convert(decl_tmp);
    cpp_saved_scope.restore();
  }
}

/*******************************************************************\

Function: cpp_typecheckt::class_template_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_typecheckt::class_template_identifier(
  const irep_idt &base_name,
  const template_typet &template_type,
  const cpp_template_args_non_tct &partial_specialization_args)
{
  std::string identifier=
    cpp_scopes.current_scope().prefix+
    "template."+id2string(base_name) + "<";

  int counter=0;

  // these are probably not needed -- templates
  // should be unique in a namespace
  for(template_typet::template_parameterst::const_iterator
      it=template_type.template_parameters().begin();
      it!=template_type.template_parameters().end();
      it++)
  {
    if(counter!=0)
      identifier+=',';

    if(it->id()==ID_type)
      identifier+="Type"+std::to_string(counter);
    else
      identifier+="Non_Type"+std::to_string(counter);

    counter++;
  }

  identifier += ">";

  if(!partial_specialization_args.arguments().empty())
  {
    identifier+="_specialized_to_<";

    counter=0;
    for(cpp_template_args_non_tct::argumentst::const_iterator
        it=partial_specialization_args.arguments().begin();
        it!=partial_specialization_args.arguments().end();
        it++, counter++)
    {
      if(counter!=0)
        identifier+=',';

      // These are not yet typechecked, as they may depend
      // on unassigned template parameters.

      if(it->id()==ID_type || it->id()=="ambiguous")
        identifier+=cpp_type2name(it->type());
      else
        identifier+=cpp_expr2name(*it);
    }

    identifier+='>';
  }

  return identifier;
}

/*******************************************************************\

Function: cpp_typecheckt::function_template_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_typecheckt::function_template_identifier(
  const irep_idt &base_name,
  const template_typet &template_type,
  const typet &function_type)
{
  // we first build something without function arguments
  cpp_template_args_non_tct partial_specialization_args;
  std::string identifier=
    class_template_identifier(base_name, template_type,
                              partial_specialization_args);

  // we must also add the signature of the function to the identifier
  identifier+=cpp_type2name(function_type);

  return identifier;
}

/*******************************************************************\

Function: cpp_typecheckt::convert_class_template_specialization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_class_template_specialization(
  cpp_declarationt &declaration)
{
  cpp_save_scopet saved_scope(cpp_scopes);

  typet &type=declaration.type();

  ASSERT(type.id()==ID_struct);

  cpp_namet &cpp_name=
    static_cast<cpp_namet &>(type.add(ID_tag));

  if(cpp_name.is_qualified())
  {
    error().source_location=cpp_name.source_location();
    error() << "qualifiers not expected here" << eom;
    throw 0;
  }

  if(cpp_name.get_sub().size()!=2 ||
     cpp_name.get_sub()[0].id()!=ID_name ||
     cpp_name.get_sub()[1].id()!=ID_template_args)
  {
    // currently we are more restrictive
    // than the standard
    error().source_location=cpp_name.source_location();
    error() << "bad template-class-sepcialization name" << eom;
    throw 0;
  }

  irep_idt base_name=
    cpp_name.get_sub()[0].get(ID_identifier);

  // copy the template arguments
  const cpp_template_args_non_tct template_args_non_tc=
    to_cpp_template_args_non_tc(cpp_name.get_sub()[1]);

  // Remove the template arguments from the name.
  cpp_name.get_sub().pop_back();

  // get the template symbol

  cpp_scopest::id_sett id_set;
  cpp_scopes.current_scope().lookup(
    base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::TEMPLATE, id_set);

  // remove any specializations
  for(cpp_scopest::id_sett::iterator
      it=id_set.begin();
      it!=id_set.end();
      ) // no it++
  {
    cpp_scopest::id_sett::iterator next=it;
    next++;

    if(lookup((*it)->identifier).type.
         find("specialization_of").is_not_nil())
      id_set.erase(it);

    it=next;
  }

  // only one should be left
  if(id_set.empty())
  {
    error().source_location=type.source_location();
    error() << "class template `" << base_name << "' not found" << eom;
    throw 0;
  }
  else if(id_set.size()>1)
  {
    error().source_location=type.source_location();
    error() << "class template `" << base_name << "' is ambiguous"
            << eom;
    throw 0;
  }

  symbol_tablet::symbolst::iterator s_it=
    symbol_table.symbols.find((*id_set.begin())->identifier);

  ASSERT(s_it!=symbol_table.symbols.end());

  symbolt &template_symbol=s_it->second;

  if(!template_symbol.type.get_bool(ID_is_template))
  {
    error().source_location=type.source_location();
    error() << "expected a template" << eom;
  }

  #if 0
  // is this partial specialization?
  if(declaration.template_type().parameters().empty())
  {
    // typecheck arguments -- these are for the 'primary' template!
    cpp_template_args_tct template_args_tc=
      typecheck_template_args(
        declaration.source_location(),
        to_cpp_declaration(template_symbol.type).template_type(),
        template_args_non_tc);

    // Full specialization, i.e., template<>.
    // We instantiate.
    instantiate_template(
      cpp_name.source_location(),
      template_symbol,
      template_args_tc,
      type);
  }
  else // NOLINT(readability/braces)
  #endif

  {
    // partial specialization -- we typecheck
    declaration.partial_specialization_args()=template_args_non_tc;
    declaration.set_specialization_of(template_symbol.name);

    typecheck_class_template(declaration);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::convert_template_function_or_member_specialization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_template_function_or_member_specialization(
  cpp_declarationt &declaration)
{
  cpp_save_scopet saved_scope(cpp_scopes);

  if(declaration.declarators().size()!=1 ||
     declaration.declarators().front().type().id()!=ID_function_type)
  {
    error().source_location=declaration.type().source_location();
    error() << "expected function template specialization" << eom;
    throw 0;
  }

  ASSERT(declaration.declarators().size()==1);
  cpp_declaratort declarator=declaration.declarators().front();
  cpp_namet &cpp_name=declarator.name();

  if(cpp_name.is_qualified())
  {
    error().source_location=cpp_name.source_location();
    error() << "qualifiers not expected here" << eom;
    throw 0;
  }

  // There is specialization (instantiation with template arguments)
  // but also function overloading (no template arguments)

  ASSERT(!cpp_name.get_sub().empty());

  if(cpp_name.get_sub().back().id()==ID_template_args)
  {
    // proper specialization with arguments
    if(cpp_name.get_sub().size()!=2 ||
       cpp_name.get_sub()[0].id()!=ID_name ||
       cpp_name.get_sub()[1].id()!=ID_template_args)
    {
      // currently we are more restrictive
      // than the standard
      error().source_location=cpp_name.source_location();
      error() << "bad template-function-specialization name" << eom;
      throw 0;
    }

    std::string base_name=
      cpp_name.get_sub()[0].get(ID_identifier).c_str();

    cpp_scopest::id_sett id_set;
    cpp_scopes.current_scope().lookup(
      base_name, cpp_scopet::SCOPE_ONLY, id_set);

    if(id_set.empty())
    {
      error().source_location=cpp_name.source_location();
      error() << "template function `" << base_name << "' not found"
              << eom;
      throw 0;
    }
    else if(id_set.size()>1)
    {
      error().source_location=cpp_name.source_location();
      error() << "template function `" << base_name
              << "' is ambiguous" << eom;
      throw 0;
    }

    const symbolt &template_symbol=
      lookup((*id_set.begin())->identifier);

    cpp_template_args_tct template_args=
      typecheck_template_args(
        declaration.source_location(),
        template_symbol,
        to_cpp_template_args_non_tc(cpp_name.get_sub()[1]));

    cpp_name.get_sub().pop_back();

    typet specialization;
    specialization.swap(declarator);

    instantiate_template(
      cpp_name.source_location(),
      template_symbol,
      template_args,
      template_args,
      specialization);
  }
  else
  {
    // Just overloading, but this is still a template
    // for disambiguation purposes!
    // http://www.gotw.ca/publications/mill17.htm
    cpp_declarationt new_declaration=declaration;

    new_declaration.remove(ID_template_type);
    new_declaration.remove(ID_is_template);
    new_declaration.set(ID_C_template, ""); // todo, get identifier

    convert_non_template_declaration(new_declaration);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_template_parameters

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_scopet &cpp_typecheckt::typecheck_template_parameters(
  template_typet &type)
{
  cpp_save_scopet cpp_saved_scope(cpp_scopes);

  ASSERT(type.id()==ID_template);

  std::string id_suffix="template::"+std::to_string(template_counter++);

  // produce a new scope for the template parameters
  cpp_scopet &template_scope=
    cpp_scopes.current_scope().new_scope(
      cpp_scopes.current_scope().prefix+id_suffix);

  template_scope.prefix=template_scope.get_parent().prefix+id_suffix;
  template_scope.id_class=cpp_idt::TEMPLATE_SCOPE;

  cpp_scopes.go_to(template_scope);

  // put template parameters into this scope
  template_typet::template_parameterst &parameters=
    type.template_parameters();

  unsigned anon_count=0;

  for(template_typet::template_parameterst::iterator
      it=parameters.begin();
      it!=parameters.end();
      it++)
  {
    exprt &parameter=*it;

    cpp_declarationt declaration;
    declaration.swap(static_cast<cpp_declarationt &>(parameter));

    cpp_declarator_convertert cpp_declarator_converter(*this);

    // there must be _one_ declarator
    ASSERT(declaration.declarators().size()==1);

    cpp_declaratort &declarator=declaration.declarators().front();

    // it may be anonymous
    if(declarator.name().is_nil())
    {
      irept name(ID_name);
      name.set(ID_identifier, "anon#"+std::to_string(++anon_count));
      declarator.name()=cpp_namet();
      declarator.name().get_sub().push_back(name);
    }

    #if 1
    // The declarator needs to be just a name
    if(declarator.name().get_sub().size()!=1 ||
       declarator.name().get_sub().front().id()!=ID_name)
    {
      error().source_location=declaration.source_location();
      error() << "template parameter must be simple name" << eom;
      throw 0;
    }

    cpp_scopet &scope=cpp_scopes.current_scope();

    irep_idt base_name=declarator.name().get_sub().front().get(ID_identifier);
    irep_idt identifier=scope.prefix+id2string(base_name);

    // add to scope
    cpp_idt &id=scope.insert(base_name);
    id.identifier=identifier;
    id.id_class=cpp_idt::TEMPLATE_PARAMETER;

    // is it a type or not?
    if(declaration.get_bool(ID_is_type))
    {
      parameter=exprt(ID_type, typet(ID_symbol));
      parameter.type().set(ID_identifier, identifier);
      parameter.type().add_source_location()=declaration.find_source_location();
    }
    else
    {
      // The type is not checked, as it might depend
      // on earlier parameters.
      typet type=declaration.type();
      parameter=symbol_exprt(identifier, type);
    }

    // There might be a default type or default value.
    // We store it for later, as it can't be typechecked now
    // because of possible dependencies on earlier parameters!
    if(declarator.value().is_not_nil())
      parameter.add(ID_C_default_value)=declarator.value();

    #else
    // is it a type or not?
    cpp_declarator_converter.is_typedef=declaration.get_bool(ID_is_type);

    // say it a template parameter
    cpp_declarator_converter.is_template_parameter=true;

    // There might be a default type or default value.
    // We store it for later, as it can't be typechecked now
    // because of possible dependencies on earlier parameters!
    exprt default_value=declarator.value();
    declarator.value().make_nil();

    const symbolt &symbol=
      cpp_declarator_converter.convert(declaration, declarator);

    if(cpp_declarator_converter.is_typedef)
    {
      parameter=exprt(ID_type, typet(ID_symbol));
      parameter.type().set(ID_identifier, symbol.name);
      parameter.type().add_source_location()=declaration.find_location();
    }
    else
      parameter=symbol.symbol_expr();

    // set (non-typechecked) default value
    if(default_value.is_not_nil())
      parameter.add(ID_C_default_value)=default_value;

    parameter.add_source_location()=declaration.find_location();
    #endif
  }

  // continue without adding to the prefix
  template_scope.prefix=template_scope.get_parent().prefix;

  return template_scope;
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_template_args

  Inputs: location, non-typechecked template arguments

 Outputs: typechecked template arguments

 Purpose:

\*******************************************************************/

cpp_template_args_tct cpp_typecheckt::typecheck_template_args(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_non_tct &template_args)
{
  // old stuff
  ASSERT(template_args.id()!=ID_already_typechecked);

  ASSERT(template_symbol.type.get_bool(ID_is_template));

  const template_typet &template_type=
    to_cpp_declaration(template_symbol.type).template_type();

  // bad re-cast, but better than copying the args one by one
  cpp_template_args_tct result=
    (const cpp_template_args_tct &)(template_args);

  cpp_template_args_tct::argumentst &args=
    result.arguments();

  const template_typet::template_parameterst &parameters=
    template_type.template_parameters();

  if(parameters.size()<args.size())
  {
    error().source_location=source_location;
    error() << "too many template arguments (expected "
            << parameters.size() << ", but got "
            << args.size() << ")" << eom;
    throw 0;
  }

  // we will modify the template map
  template_mapt old_template_map;
  old_template_map=template_map;

  // check for default arguments
  for(std::size_t i=0; i<parameters.size(); i++)
  {
    const template_parametert &parameter=parameters[i];
    cpp_save_scopet cpp_saved_scope(cpp_scopes);

    if(i>=args.size())
    {
      // Check for default argument for the parameter.
      // These may depend on previous arguments.
      if(!parameter.has_default_argument())
      {
        error().source_location=source_location;
        error() << "not enough template arguments (expected "
                << parameters.size() << ", but got " << args.size()
                << ")" << eom;
        throw 0;
      }

      args.push_back(parameter.default_argument());

      // these need to be typechecked in the scope of the template,
      // not in the current scope!
      cpp_idt *template_scope=cpp_scopes.id_map[template_symbol.name];
      ASSERT(template_scope!=NULL);
      cpp_scopes.go_to(*template_scope);
    }

    ASSERT(i<args.size());

    exprt &arg=args[i];

    if(parameter.id()==ID_type)
    {
      if(arg.id()==ID_type)
      {
        typecheck_type(arg.type());
      }
      else if(arg.id()=="ambiguous")
      {
        typecheck_type(arg.type());
        typet t=arg.type();
        arg=exprt(ID_type, t);
      }
      else
      {
        error().source_location=arg.source_location();
        error() << "expected type, but got expression" << eom;
        throw 0;
      }
    }
    else // expression
    {
      if(arg.id()==ID_type)
      {
        error().source_location=arg.source_location();
        error() << "expected expression, but got type" << eom;
        throw 0;
      }
      else if(arg.id()=="ambiguous")
      {
        exprt e;
        e.swap(arg.type());
        arg.swap(e);
      }

      typet type=parameter.type();

      // First check the parameter type (might have ealier
      // type parameters in it). Needs to be checked in scope
      // of template.
      {
        cpp_save_scopet cpp_saved_scope(cpp_scopes);
        cpp_idt *template_scope=cpp_scopes.id_map[template_symbol.name];
        ASSERT(template_scope!=NULL);
        cpp_scopes.go_to(*template_scope);
        typecheck_type(type);
      }

      // Now check the argument to match that.
      typecheck_expr(arg);
      simplify(arg, *this);
      implicit_typecast(arg, type);
    }

    // Set right away -- this is for the benefit of default
    // arguments and later parameters whose type might
    // depend on an earlier parameter.

    template_map.set(parameter, arg);
  }

  // restore template map
  template_map.swap(old_template_map);

  // now the numbers should match
  ASSERT(args.size()==parameters.size());

  return result;
}

/*******************************************************************\

Function: cpp_typecheckt::convert_template_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert_template_declaration(
  cpp_declarationt &declaration)
{
  ASSERT(declaration.is_template());

  if(declaration.member_spec().is_virtual())
  {
    error().source_location=declaration.source_location();
    error() <<  "invalid use of 'virtual' in template declaration"
            << eom;
    throw 0;
  }

  if(declaration.is_typedef())
  {
    error().source_location=declaration.source_location();
    error() << "template declaration for typedef" << eom;
    throw 0;
  }

  typet &type=declaration.type();

  // there are
  // 1) function templates
  // 2) class templates
  // 3) template members of class templates (static or methods)
  // 4) variable templates (C++14)

  if(declaration.is_class_template())
  {
    // there should not be declarators
    if(!declaration.declarators().empty())
    {
      error().source_location=declaration.source_location();
      error() << "class template not expected to have declarators"
              << eom;
      throw 0;
    }

    // it needs to be a class template
    if(type.id()!=ID_struct)
    {
      error().source_location=declaration.source_location();
      error() << "expected class template" << eom;
      throw 0;
    }

    // Is it class template specialization?
    // We can tell if there are template arguments in the class name,
    // like template<...> class tag<stuff> ...
    if((static_cast<const cpp_namet &>(
       type.find(ID_tag))).has_template_args())
    {
      convert_class_template_specialization(declaration);
      return;
    }

    typecheck_class_template(declaration);
    return;
  }
  // maybe function template, maybe class template member, maye
  // template variable
  else
  {
    // there should be declarators in either case
    if(declaration.declarators().empty())
    {
      error().source_location=declaration.source_location();
      error() << "non-class template is expected to have a declarator"
              << eom;
      throw 0;
    }

    // Is it function template specialization?
    // Only full specialization is allowed!
    if(declaration.template_type().template_parameters().empty())
    {
      convert_template_function_or_member_specialization(declaration);
      return;
    }

    // Explicit qualification is forbidden for function templates,
    // which we can use to distinguish them.

    ASSERT(declaration.declarators().size()>=1);

    cpp_declaratort &declarator=declaration.declarators()[0];
    const cpp_namet &cpp_name=to_cpp_name(declarator.add(ID_name));

    if(cpp_name.is_qualified() ||
       cpp_name.has_template_args())
      return typecheck_class_template_member(declaration);

    // must be function template
    typecheck_function_template(declaration);
    return;
  }
}
