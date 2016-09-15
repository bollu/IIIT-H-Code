class Question < ApplicationRecord
    validates :question, presence: true, length: {minimum: 1} 
    validates :index, presence: true
    belongs_to :suvey 
end
