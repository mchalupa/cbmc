int main()
{
  int i;

  __CPROVER_assume(i>=0);

  while(i != 10000)
    __CPROVER_loop_invariant(i>=0) // should pass
  {
    __CPROVER_assert(i >= 0, "property 1"); // should pass
  }

  return 0;
}
