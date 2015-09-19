#include <string>
#include <iostream>
#include <istream>
#include <ostream>
#include <iterator>

#include "Mesh.hpp"
#include "IR.hpp"
#include "TypeInfo.hpp"

int main() {
  // don't skip the whitespace while reading
  std::cin >> std::noskipws;

  // use stream iterators to copy the stream to a string
  std::istream_iterator<char> it(std::cin);
  std::istream_iterator<char> end;
  std::string results(it, end);

  try {
    json jobjIn = json::parse(results);
    std::shared_ptr<Pipeline> b = fromJSON(W<std::shared_ptr<Pipeline>>(),jobjIn);
    std::shared_ptr<data::Pipeline> tv = std::static_pointer_cast<data::Pipeline>(b);
    json jobjOut = toJSON(b);
    std::cout << jobjOut;
  } catch (std::string e) {
    std::cout << "exception: " << e << "\n";
  } catch (...) { std::cout << "default exception\n"; }

  return 0;
}
