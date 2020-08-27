/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

\*******************************************************************/

/// \file
/// This is a skeleton implementaion of an abstract interpretation
/// domain.  It is intended to be a start-point for writing your own
/// domain!

#ifndef CPROVER_ANALYSES_EXAMPLE_DOMAIN_H
#define CPROVER_ANALYSES_EXAMPLE_DOMAIN_H

#include "ai_domain.h"

class example_domaint : public ai_domain_baset
{
public:
  /// Constructors
  example_domaint();

  /// Destructor
  virtual ~example_domaint();

  /// Transform updates the domain with the effect of the instruction "from"
  void transform(
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) override;

  /// Merges two domains together
  /// \return true if and only if *this has been modified / extended
  bool merge(const example_domaint &b, locationt, locationt);

  /// Set the domain to be empty, i.e. representing nothing
  void make_bottom() override;

  /// Set the domain to allow all possibilities
  void make_top() override;

  /// Set up the domain for the start of the program
  void make_entry() override;

  /// Is the domain bottom or not
  bool is_bottom() const override;

  /// Is the domain top or not
  bool is_top() const override;

  /// Output the domain as a string
  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;
};

#endif // CPROVER_ANALYSES_EXAMPLE_DOMAIN_H
