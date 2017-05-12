/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_SUBSTITUTE_H
#define CPROVER_UTIL_SUBSTITUTE_H

#include <string>
#include "invariant.h"

void substitute(
  std::string &dest,
  const std::string &what,
  const std::string &by);

#endif // CPROVER_UTIL_SUBSTITUTE_H
