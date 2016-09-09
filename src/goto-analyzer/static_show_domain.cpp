/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#include <fstream>

#include <util/message.h>
#include <util/json.h>
#include <util/xml.h>

#include <analyses/interval_domain.h>
#include <analyses/constant_propagator.h>

#include "static_show_domain.h"

/*******************************************************************\

Function: static_show_domain

  Inputs: The goto_model to analyze, options giving the domain and output,
          the message handler and output stream.

 Outputs: The abstract domain via out.

 Purpose: Runs the analyzer and then prints out the domain.

\*******************************************************************/

bool static_show_domain(
  const goto_modelt &goto_model,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  ai_baset *domain = NULL;
  
  if (options.get_bool_option("sequential"))
  {
    if (options.get_bool_option("constants"))
      domain = new ait<constant_propagator_domaint>();
    
    else if (options.get_bool_option("intervals"))
      domain = new ait<interval_domaint>();
    
    //else if (options.get_bool_option("non-null"))
    //  domain = new ait<non_null_domaint>();
    
  }
  else if (options.get_bool_option("concurrent"))
  {
    // Constant and interval don't have merge_shared yet
#if 0
    if (options.get_bool_option("constants"))
      domain = new concurrency_aware_ait<constant_propagator_domaint>();
    
    else if (options.get_bool_option("intervals"))
      domain = new concurrency_aware_ait<interval_domaint>();
    
    //else if (options.get_bool_option("non-null"))
    //  domain = new concurrency_aware_ait<non_null_domaint>();    
#endif
  }

  if (domain == NULL)
    return true;

  //status() << "performing analysis" << eom;
  (*domain)(goto_model);

  if(options.get_bool_option("json"))
    out << domain->output_json(goto_model);
  else if(options.get_bool_option("xml"))
    out << domain->output_xml(goto_model);
  else
    domain->output(goto_model, out);

  delete domain;
  return false;
}
