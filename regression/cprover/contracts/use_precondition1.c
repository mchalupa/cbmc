void my_function(int parameter)
  __CPROVER_requires(parameter >= 10)
{
  __CPROVER_assert(parameter != 0, "property 1");  // passes
  __CPROVER_assert(parameter != 20, "property 2"); // fails
}
