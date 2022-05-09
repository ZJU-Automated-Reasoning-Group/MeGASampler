
#ifndef MEGASAMPLER_INTERVALMAP_H
#define MEGASAMPLER_INTERVALMAP_H

#include <z3++.h>
#include "interval.h"

namespace std {
    template <>
    struct hash<z3::expr>
    {
        std::size_t operator()(const z3::expr& e) const
        {
          return hash<string>()(e.to_string());
        }
    };
    template<>
    struct equal_to<z3::expr> {
        bool operator()(const z3::expr& lhs, const z3::expr& rhs) const {
          return z3::eq(lhs, rhs);
        }
    };
}

typedef std::unordered_map<z3::expr,Interval> IntervalMap;


#endif //MEGASAMPLER_INTERVALMAP_H
