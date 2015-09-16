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

template<> String fromJSON<String>(String &v, json &obj) {
  String s;
  return s;
}

template<> Float fromJSON<Float>(Float &v, json &obj) {
  return 0.0;
}

template<> bool fromJSON<bool>(bool &v, json &obj) {
  return false;
}

template<> int fromJSON<int>(int &v, json &obj) {
  return 0;
}

template<> unsigned int fromJSON<unsigned int>(unsigned int &v, json &obj) {
  return 0;
}

