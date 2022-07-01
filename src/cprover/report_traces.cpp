/*******************************************************************\

Module: Report Traces

Author:

\*******************************************************************/

/// \file
/// Solver

#include "report_traces.h"

#include <util/format_expr.h>

#include "console.h"
#include "state.h"

#include <iomanip>

optionalt<exprt> address_to_lvalue(exprt src)
{
  if(src.id() == ID_object_address)
    return to_object_address_expr(src).object_expr();
  else if(src.id() == ID_field_address)
  {
    const auto &field_address_expr = to_field_address_expr(src);
    auto compound_opt = address_to_lvalue(field_address_expr.base());
    if(compound_opt.has_value())
      return member_exprt(
        *compound_opt,
        field_address_expr.component_name(),
        field_address_expr.field_type());
    else
      return {};
  }
  else if(src.id() == ID_element_address)
  {
    const auto &element_address_expr = to_element_address_expr(src);
    auto array_opt = address_to_lvalue(element_address_expr.base());
    if(array_opt.has_value())
      return index_exprt(
        *array_opt,
        element_address_expr.index(),
        element_address_expr.element_type());
    else
      return {};
  }
  else
    return {};
}

void show_trace(
  const std::vector<framet> &frames,
  const propertyt &property,
  const namespacet &ns)
{
  irep_idt function_id, file;

  for(auto &step : property.trace)
  {
    const auto &frame = frames[step.frame.index];

    if(
      frame.source_location.get_function() != function_id ||
      frame.source_location.get_file() != file)
    {
      consolet::out() << consolet::faint << frame.source_location.get_file();
      if(frame.source_location.get_function() != "")
        consolet::out() << " function " << frame.source_location.get_function();
      consolet::out() << consolet::reset << '\n';
      file = frame.source_location.get_file();
      function_id = frame.source_location.get_function();
    }

    consolet::out() << consolet::faint << std::setw(4)
                    << frame.source_location.get_line() << consolet::reset
                    << ' ';

    if(step.updates.empty())
    {
      bool first = true;
      for(auto &implication : frame.implications)
      {
        if(first)
          first = false;
        else
        {
          consolet::out() << std::setw(4) << ' ';
        }
        consolet::out() << "constraint: " << format(implication.as_expr())
                        << '\n';
      }
    }
    else
    {
      bool first = true;
      for(auto &update : step.updates)
      {
        if(first)
          first = false;
        else
        {
          consolet::out() << std::setw(4) << ' ';
        }

        auto lvalue_opt = address_to_lvalue(update.address);
        if(lvalue_opt.has_value())
          consolet::out() << format(*lvalue_opt);
        else
          consolet::out() << '[' << format(update.address) << ']';

        consolet::out() << " := " << format(update.value);
        consolet::out() << '\n';
      }
    }
  }
}

void report_traces(
  const std::vector<framet> &frames,
  const std::vector<propertyt> &properties,
  const namespacet &ns)
{
  for(auto &property : properties)
  {
    if(property.status == propertyt::REFUTED)
    {
      consolet::out() << '\n'
                      << "Trace for " << consolet::bold
                      << property.property_id() << consolet::reset << ':'
                      << '\n';

      show_trace(frames, property, ns);
    }
  }
}
