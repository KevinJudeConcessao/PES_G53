#include <iostream>
#include "reflection.hpp"

enum Fruits {
  Apples,
  Oranges,
  Bananas
};

int main() {
  auto reflected_fruits = std::reflexpr<Fruits>();
  std::cout << "The type is " << reflected_fruits.name() << std::endl;
  std::cout << "There are " << reflected_fruits.size() << std::endl;
  auto fruit = reflected_fruits.begin();
  std::cout << "The first fruit is " << fruit.name() << std::endl;
}
