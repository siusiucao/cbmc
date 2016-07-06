/*******************************************************************\

Module: Compute the dependency graph

Author: Martin Brain

Date: March 2016

\*******************************************************************/


#include <analyses/dependence_graph.h>

#include <util/json.h>

#include "dependence_graph_analysis.h"

/*******************************************************************\

Function: data_flow_analysis

  Inputs: The program to analyse, its namespace, the type of graph,
          a Boolean for JSON output and an output stream.

 Outputs: None

 Purpose: Uses dependence_graph to perform the analysis and then 
          formats the output appropriately.

\*******************************************************************/

void dependence_graph_analysis(
  const goto_modelt &goto_model,
  const dependence_graph_typet dgt,
  const bool json,
  std::ostream &os)
{
  namespacet ns(goto_model.symbol_table);
  
  // Perform the analysis
  dependence_grapht dependence_graph(ns);
  dependence_graph(goto_model.goto_functions, ns);

  // TODO : refactor the JSON output into the dependency graph
  // Output
  if (json)
  {
    json_arrayt json_result;

    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      json_objectt &function_graph=json_result.push_back().make_object();

      function_graph["function"]=json_stringt(id2string(f_it->first));
      //      function_graph["file name"]=
      //	json_stringt(id2string(f_it->second.body.instructions.begin().source_location.get_file()));
      
      
      if(f_it->second.body_available())
      {
	json_arrayt &graph=function_graph["graph"].make_array();

	forall_goto_program_instructions(i_it, f_it->second.body)
	{
	  const dep_graph_domaint &dep(dependence_graph[i_it]);
	  
	  if (((dgt == DEPENDENCE_GRAPH_CONTROL) || (dgt == DEPENDENCE_GRAPH_BOTH)) &&
	      !dep.control_deps.empty())
	  {
	    for(dep_graph_domaint::depst::const_iterator
		  cdi=dep.control_deps.begin();
		cdi!=dep.control_deps.end();
		++cdi)
	    {
	      json_objectt &link=graph.push_back().make_object();
	      link["from"]=json_stringt(i_it->source_location.as_string());
	      link["to"]=json_stringt((*cdi)->source_location.as_string());
	      link["type"]=json_stringt("control");
	    }
	  }

	  if (((dgt == DEPENDENCE_GRAPH_DATA) || (dgt == DEPENDENCE_GRAPH_BOTH)) &&
	      !dep.data_deps.empty())
	  {
	    for(dep_graph_domaint::depst::const_iterator
		  ddi=dep.data_deps.begin();
		ddi!=dep.data_deps.end();
		++ddi)
	    {
	      json_objectt &link=graph.push_back().make_object();
	      link["from"]=json_stringt(i_it->source_location.as_string());
	      link["to"]=json_stringt((*ddi)->source_location.as_string());
	      link["type"]=json_stringt("data");
	    }
	  }
	}
	
	function_graph["status"]=json_stringt("analysed");
      }
      else
      {
	function_graph["status"]=json_stringt("no body provided");
      }
    }
    
    if(!json_result.array.empty())
      os << json_result << std::endl;
  }
  else
  {
    // The old goto-instrument output format
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      if(f_it->second.body_available())
      {
	os << "////" << std::endl;
	os << "//// Function: " << f_it->first << std::endl;
	os << "////" << std::endl;
	os << std::endl;
	dependence_graph.output(ns, f_it->second.body, os);
      }
    }
    
    dependence_graph.output_dot(os);
  }

  return;
}

