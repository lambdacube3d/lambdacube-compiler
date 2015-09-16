#ifndef HEADER_RT_H
#define HEADER_RT_H

#include <vector>
#include <map>
#include <string>

#include "json.hpp"

using json = nlohmann::json;

typedef int Int;
typedef int Int32;
typedef unsigned int Word;
typedef unsigned int Word32;
typedef float Float;
typedef bool Bool;
typedef std::string String;

template<typename T>
json toJSON(T &v);

template<typename any>
json toJSON(std::vector<any> &v) {
  json obj = json::array();
  for (any i : v) {
    obj.push_back(toJSON(i));
  }
  return obj;
}

template<typename k, typename v>
json toJSON(std::map<k,v> &value) {
  return json();
}

template<typename T>
T fromJSON(T &v, json &obj);

template<typename any>
std::vector<any> fromJSON(std::vector<any> &v, json &obj) {
  std::vector<any> a;
  return a;
}

template<typename k, typename v>
std::map<k,v> fromJSON(std::map<k,v> &value, json &obj) {
  std::map<k,v> a;
  return a;
}

#endif