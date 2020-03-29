#!/usr/bin/env python2.7
import pyspark
from pyspark.sql import *
import argparse


parser = argparse.ArgumentParser(description='solve question.')
parser.add_argument('outpath', type=str, metavar='O', help='path to output')
parser.add_argument('--ncpu',  type=int, default=2,
                    help='number of cpus')

args = parser.parse_args()

spark = SparkSession.builder \
  .master("local") \
  .appName("Word Count") \
  .config("spark.some.config.option", "some-value") \
  .getOrCreate()


airports = spark.read.csv("Dataset/airports.csv",
        header=True,
        inferSchema=True)

df = airports.filter((airports.LATITUDE >= 10) & (airports.LATITUDE <= 90) & (airports.LONGITUDE <= -10) & (airports.LONGITUDE >= -90))
# df = airports.filter((airports.LATITUDE >= 10) & (airports.LATITUDE <= 90))
df.toPandas().to_csv(args.outpath, index=False, encoding='utf-8')

