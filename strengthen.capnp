# strengthen.capnp
@0xb47e2e74b35f3016;

struct StrengthenResult {
  res @0 :Bool;
  failuredecription @1 :Text;
  intervalmap @2 :List(VarInterval);
  unsimplified @3 :Text;

  struct VarInterval {
    varsort @0 :Text;
    variable @1 :Text;
    index @2 :Text;
    interval @3 :Interval;

    struct Interval {
      islowminf @0 :Bool;
      ishighinf @1 :Bool;
      low @2 :Int64;
      high @3 :Int64;
    }
  }
}
