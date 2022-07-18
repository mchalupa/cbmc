int my_function(int parameter)
  __CPROVER_ensures(__CPROVER_return_value == 123)
{
  return parameter;
}
