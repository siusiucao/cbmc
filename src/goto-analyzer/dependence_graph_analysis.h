/*******************************************************************\

Module: Compute the dependency graph

Author: Martin Brain

Date: March 2016

\*******************************************************************/

#ifndef CPROVER_DEPENDENCE_GRAPH_ANALYSIS_H
#define CPROVER_DEPENDENCE_GRAPH_ANALYSIS_H

#include <ostream>

#include <goto-programs/goto_model.h>

typedef enum {
  DEPENDENCE_GRAPH_DATA,
  DEPENDENCE_GRAPH_CONTROL,
  DEPENDENCE_GRAPH_BOTH,
} dependence_graph_typet;

void dependence_graph_analysis(
  const goto_modelt &goto_model,
  const dependence_graph_typet dgt,
  const bool json,
  std::ostream &os);

#endif
