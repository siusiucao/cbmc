/*******************************************************************\

 Module: MODULE NAME

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include "abstract_value.h"
#include <util/std_expr.h>

abstract_valuet::abstract_valuet(typet t):
  abstract_objectt(t)
{}

abstract_valuet::abstract_valuet(typet t, bool tp, bool bttm):
  abstract_objectt(t, tp, bttm)
{}

abstract_valuet::abstract_valuet(const abstract_valuet &old):
  abstract_objectt(old)
{}

abstract_valuet::abstract_valuet(const constant_exprt &e):
  abstract_objectt(e)
{}
