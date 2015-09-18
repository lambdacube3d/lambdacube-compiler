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

template<typename T1>
struct Maybe
{
  T1 data;
  bool valid;
};

template<typename T>
struct V2 { T x,y; };

template<typename T>
struct V3 { T x,y,z; };

template<typename T>
struct V4 { T x,y,z,w; };

typedef struct V2<Int>    V2I;
typedef struct V2<Word>   V2U;
typedef struct V2<Float>  V2F;
typedef struct V2<Bool>   V2B;

typedef struct V3<Int>    V3I;
typedef struct V3<Word>   V3U;
typedef struct V3<Float>  V3F;
typedef struct V3<Bool>   V3B;

typedef struct V4<Int>    V4I;
typedef struct V4<Word>   V4U;
typedef struct V4<Float>  V4F;
typedef struct V4<Bool>   V4B;

typedef struct V2<V2F>    M22F;
typedef struct V2<V3F>    M32F;
typedef struct V2<V4F>    M42F;
typedef struct V3<V2F>    M23F;
typedef struct V3<V3F>    M33F;
typedef struct V3<V4F>    M43F;
typedef struct V4<V2F>    M24F;
typedef struct V4<V3F>    M34F;
typedef struct V4<V4F>    M44F;


template<typename T>
json toJSON(T &v);

template<typename any>
json toJSON(Maybe<any> &v) {
  if (v.valid) {
    return toJSON(v.data);
  }
  return json();
}

template<typename any>
json toJSON(V2<any> &v) {
  json obj({});
  obj["x"] = toJSON(v.x);
  obj["y"] = toJSON(v.y);
  return obj;
}

template<typename any>
json toJSON(V3<any> &v) {
  json obj({});
  obj["x"] = toJSON(v.x);
  obj["y"] = toJSON(v.y);
  obj["z"] = toJSON(v.z);
  return obj;
}

template<typename any>
json toJSON(V4<any> &v) {
  json obj({});
  obj["x"] = toJSON(v.x);
  obj["y"] = toJSON(v.y);
  obj["z"] = toJSON(v.z);
  obj["w"] = toJSON(v.w);
  return obj;
}

template<typename any>
json toJSON(std::vector<any> &v) {
  json obj = json::array();
  for (any i : v) {
    obj.push_back(toJSON(i));
  }
  return obj;
}

template<typename v>
json toJSON(std::map<String,v> &value) {
  json obj({});
  for(auto i : value) {
    obj[i.first] = toJSON(i.second);
  }
  return obj;
}

template<typename T>
struct W {};

template<typename T>
T fromJSON(W<T> w, json &obj);

template<typename any>
Maybe<any> fromJSON(W<Maybe<any>> v, json &obj) {
  Maybe<any> a;
  if (obj.is_null()) {
    a.valid = false;
  } else {
    a.valid = true;
    a.data = fromJSON(W<any>(),obj);
  }
  return a;
}

template<typename any>
V2<any> fromJSON(W<V2<any>> v, json &obj) {
  V2<any> a;
  a.x = fromJSON(W<any>(), obj["x"]);
  a.y = fromJSON(W<any>(), obj["y"]);
  return a;
}

template<typename any>
V3<any> fromJSON(W<V3<any>> v, json &obj) {
  V3<any> a;
  a.x = fromJSON(W<any>(), obj["x"]);
  a.y = fromJSON(W<any>(), obj["y"]);
  a.z = fromJSON(W<any>(), obj["z"]);
  return a;
}

template<typename any>
V4<any> fromJSON(W<V4<any>> v, json &obj) {
  V4<any> a;
  a.x = fromJSON(W<any>(), obj["x"]);
  a.y = fromJSON(W<any>(), obj["y"]);
  a.z = fromJSON(W<any>(), obj["z"]);
  a.w = fromJSON(W<any>(), obj["w"]);
  return a;
}

template<typename any>
std::vector<any> fromJSON(W<std::vector<any>> v, json &obj) {
  std::vector<any> a;
  for (json::iterator it = obj.begin(); it != obj.end(); ++it) {
    a.push_back(fromJSON(W<any>(),*it));
  }
  return a;
}

template<typename v>
std::map<String,v> fromJSON(W<std::map<String,v>> value, json &obj) {
  std::map<String,v> a;
  for (json::iterator it = obj.begin(); it != obj.end(); ++it) {
    a[it.key()] = fromJSON(W<v>(),it.value());
  }
  return a;
}

/*
template<typename k, typename v>
std::map<k,v> fromJSON(W<std::map<k,v>> value, json &obj) {
  std::map<k,v> a;
  return a;
}
*/
#endif