/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include <cassert>
#include <stdexcept>

#include "string_utils.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string strip_string(const std::string &s)
{
  std::string::size_type n=s.length();

  // find first non-space char
  unsigned i;
  for(i=0; i<n; i++)
  {
    if(!std::isspace(s[i]))
      break;
  }
  if(i==n)
    return "";

  // find last non-space char
  long j; // need signed type here
  for(j=n-1; j>=0; j--)
  {
    if(!std::isspace(s[j]))
      break;
  }

  return s.substr(i, (j-i+1));
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void split_string(
  const std::string &s,
  char delim,
  std::vector<std::string> &result,
  bool strip,
  bool remove_empty)
{
  assert(result.empty());
  assert(!std::isspace(delim));

  if(s.empty())
  {
    result.push_back("");
    return;
  }

  std::string::size_type n=s.length();
  assert(n>0);

  unsigned start=0;
  unsigned i;

  for (i=0; i<n; i++)
  {
    if (s[i]==delim)
    {
      std::string new_s=s.substr(start, i-start);

      if(strip)
        new_s=strip_string(new_s);

      if(!remove_empty || !new_s.empty())
        result.push_back(new_s);
      start=i+1;
    }
  }

  std::string new_s=s.substr(start, n-start);

  if(strip)
    new_s=strip_string(new_s);

  if(!remove_empty || !new_s.empty())
    result.push_back(new_s);

  assert(!result.empty());
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void split_string(
  const std::string &s,
  char delim,
  std::string &left,
  std::string &right,
  bool strip)
{
  assert(!std::isspace(delim));

  std::vector<std::string> result;

  split_string(s, delim, result, strip);
  if(result.size()!=2)
    throw std::invalid_argument("number of parts != 2");

  left=result[0];
  right=result[1];
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// unit tests
#if 0
int main()
{
  assert(strip_string("   x y ")=="xy");

  const std::string test=" a,, x , ,";

  std::vector<std::string> result;
  split_string(test, ',', result, false, false);
  assert(result.size()==5);
  assert(result[0]==" a");
  assert(result[1]=="");
  assert(result[2]==" x ");
  assert(result[3]==" ");
  assert(result[4]=="");

  result.clear();
  split_string(test, ',', result, true, false);
  assert(result.size()==5);
  assert(result[0]=="a");
  assert(result[1]=="");
  assert(result[2]=="x");
  assert(result[3]=="");
  assert(result[4]=="");

  result.clear();
  split_string(test, ',', result, false, true);
  assert(result.size()==3);
  assert(result[0]==" a");
  assert(result[1]==" x ");
  assert(result[2]==" ");

  split_string(test, ',', result, true, true);
  assert(result.size()==2);
  assert(result[0]=="a");
  assert(result[2]=="x");

  std::string s1;
  std::string s2;
  split_string("a:b", ':', s1, s2, false);
  assert(s1=="a");
  assert(s2=="b");
}
#endif
