class Survey < ApplicationRecord
    validates :name, presence: true, length: {minimum: 1}, uniqueness: true 
    has_many :questions
end
