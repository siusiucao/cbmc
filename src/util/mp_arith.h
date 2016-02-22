/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_MP_ARITH_H
#define CPROVER_MP_ARITH_H

#include <string>
#include <iosfwd>

#include "big-int/bigint.hh"

typedef BigInt mp_integer;

std::ostream& operator<<(std::ostream& out, const mp_integer &n);
mp_integer operator>>(const mp_integer &a, const mp_integer &b);
mp_integer operator<<(const mp_integer &a, const mp_integer &b);

const std::string integer2string(const mp_integer &n, unsigned base=10);
const mp_integer string2integer(const std::string &n, unsigned base=10);
const std::string integer2binary(const mp_integer &n, std::size_t width);
const mp_integer binary2integer(const std::string &n, bool is_signed);
mp_integer::ullong_t integer2long(const mp_integer &n);
unsigned integer2unsigned(const mp_integer &n);

#endif
