
#include "interval.h"
#include <random>

void Interval::set_upper_bound(int64_t u_bound) {
  if (u_bound < high){
    high = u_bound;
  }
}

void Interval::set_lower_bound(int64_t l_bound) {
  if (l_bound > low){
    low = l_bound;
  }
}

std::ostream &operator<<(std::ostream &os, const Interval &interval) {
  if (interval.is_bottom()){
    os << "EMPTY";
    return os;
  }
  os << "[";
  if (interval.is_low_minf()){
    os << "MINF";
  } else {
    os << interval.low;
  }
  os << ",";
  if (interval.is_high_inf()){
    os << "INF";
  } else {
    os << interval.high;
  }
  os << "]";
  return os;
}

bool Interval::is_high_inf() const {
  return high == INT64_MAX;
}

bool Interval::is_low_minf() const {
  return low == INT64_MIN;
}

bool Interval::is_bottom() const {
  return high < low;
}

bool Interval::is_top() const {
  return is_high_inf() && is_low_minf();
}

bool Interval::is_in_range(int64_t val) const {
    return (val >= low && val <= high);
}

int64_t Interval::random_in_range() const {
    std::mt19937 rng(std::random_device{}());
    std::uniform_int_distribution<int64_t> gen(low, high);  // uniform, unbiased
    return gen(rng);
}

bool Interval::is_infinite() const {
  return is_high_inf() || is_low_minf();
}
