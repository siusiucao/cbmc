/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_GOTO_ANALYZER_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H
#define CPROVER_GOTO_ANALYZER_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H

#include <map>
#include <memory>

#include <analyses/ai.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>

class variable_sensitivity_domaint : public ai_domain_baset, public messaget
{
public:
  variable_sensitivity_domaint(message_handlert &message_handler);

  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) override;

  // no states
  virtual void make_bottom() override;

  // all states -- the analysis doesn't use this,
  // and domains may refuse to implement it.
  virtual void make_top() override;

  // a reasonable entry-point state
  virtual void make_entry() override;

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override;

  virtual bool merge(
    const variable_sensitivity_domaint &b,
    locationt from,
    locationt to);

private:
  abstract_environmentt abstract_state;
};

#endif // CPROVER_GOTO_ANALYZER_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_DOMAIN_H // NOLINT(*)
