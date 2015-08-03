int nondet_int();

// Sketch pattern (allows to synthesise multiple functions - orthogonal to grammar!)
static int result;
static int __CPROVER_synthesis_arg_x;
static int __CPROVER_synthesis_arg_y;

int __CPROVER_synthesis_learn();  // To synthesise

void __CPROVER_synthesis_root()
{
  __CPROVER_synthesis_learn();
  if (result) result=__CPROVER_synthesis_arg_x;
  else result=__CPROVER_synthesis_arg_y;
}
// Sketch pattern

int main(void)
{
  __CPROVER_synthesis_arg_x=nondet_int();
  __CPROVER_synthesis_arg_y=nondet_int();
  __CPROVER_synthesis_root();
  __CPROVER_assert(
      result >= __CPROVER_synthesis_arg_x && result >= __CPROVER_synthesis_arg_y
          && (result == __CPROVER_synthesis_arg_x
              || result == __CPROVER_synthesis_arg_y), "");
  return 0;
}
