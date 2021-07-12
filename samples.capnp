# samples.capnp
@0xc1f90dd4f75e1974;

struct SampleContainer {
  samples @0 :List(Sample);
  comment @1 :Text;
  ctime @2 :UInt64;

  struct Sample {
    id @0 :UInt64;
    variables @1 :List(Variable);

    struct Variable {
      symbol @0 :Text;
      value @1 :Int64;
    }
  }
}
