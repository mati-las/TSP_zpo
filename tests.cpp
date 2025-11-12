#include <gtest/gtest.h>

#include "TSP.hxx"

TEST(CostMatrixTest, reduce_rows) {
    cost_matrix_t cm_raw = {
            {INF, 10,  8,   19,  12},
            {10,  INF, 20,  6,   3},
            {8,   20,  INF, 4,   2},
            {19,  6,   4,   INF, 7},
            {12,  3,   2,   7,   INF}
    };
    CostMatrix cm(cm_raw);

    EXPECT_EQ(cm.reduce_rows(), 19);
}