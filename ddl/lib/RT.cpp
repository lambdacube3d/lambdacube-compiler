#include "RT.hpp"

template<> json toJSON<String>(String &v) {
  return json(v);
}

template<> json toJSON<Float>(Float &v) {
  return json(v);
}

template<> json toJSON<bool>(bool &v) {
  return json(v);
}

template<> json toJSON<int>(int &v) {
  return json(v);
}

template<> json toJSON<unsigned int>(unsigned int &v) {
  return json(v);
}


